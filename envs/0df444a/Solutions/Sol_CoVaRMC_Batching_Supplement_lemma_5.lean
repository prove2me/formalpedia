-- Prove2me | solution 1 for CoVaRMC.Batching.Supplement.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:09.61011+00:00
-- url     : https://prove2.me/submissions/aa104105-abe1-4413-af8f-106d4716e7b2

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

open CoVaRMC
open CoVaRMC.Batching
open CoVaRMC.Batching.Supplement

/-- Lemma 5, pp. 15–16, Equation (23): for `γ_{1d} > 0`, at every value `w` of `(Z_1, …, Z_{d-1})`
with `g*(w) ≠ x`, `P_ε / (2ε) → q₁ + q₂` as `ε → 0⁺`. -/
theorem solution {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d) (x : ℝ) (w : Fin d' → ℝ)
    (hw : M.gStar w ≠ x) :
    Tendsto (fun ε => Peps M x w ε / (2 * ε)) (𝓝[>] 0) (𝓝 (M.q1 w x + M.q2 w x)) := by
      set a := M.γ1d with ha_def
      set b := M.δ1d with hb_def
      set c := M.xi1 w with hc_def
      have hX : ∀ z, M.X w z = c + b * z + a * z ^ 2 := fun z => rfl
      have hgs : M.gStar w = c - b ^ 2 / (4 * a) := rfl
      have hXg : ∀ z, M.gStar w ≤ M.X w z := by
        intro z
        rw [hX, hgs]
        have : c + b * z + a * z ^ 2 - (c - b ^ 2 / (4 * a)) = a * (z + b / (2 * a)) ^ 2 := by
          field_simp; ring
        nlinarith [mul_nonneg hγ.le (sq_nonneg (z + b / (2 * a)))]
      rcases lt_or_gt_of_ne hw with hlt | hgt
      · set φ : ℝ → ℝ := gaussianPDFReal 0 1 with hφ_def
        have hφc : Continuous φ := by
          rw [hφ_def]; unfold gaussianPDFReal; fun_prop
        set Φ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hΦ_def
        set D : ℝ → ℝ := fun t => b ^ 2 + 4 * a * (t - c) with hD_def
        set R1 : ℝ → ℝ := fun t => (-b - √(D t)) / (2 * a) with hR1_def
        set R2 : ℝ → ℝ := fun t => (-b + √(D t)) / (2 * a) with hR2_def
        set H : ℝ → ℝ := fun t => Φ (R2 t) - Φ (R1 t) with hH_def
        have hDx : 0 < D x := by
          rw [hgs] at hlt
          have h1 : b ^ 2 / (4 * a) * (4 * a) = b ^ 2 := by field_simp
          simp only [hD_def]
          nlinarith
        -- roots
        have hfac : ∀ t z, 0 ≤ D t →
            c + b * z + a * z ^ 2 - t = a * ((z - R1 t) * (z - R2 t)) := by
          intro t z hDt
          have hs := Real.sq_sqrt hDt
          simp only [hR1_def, hR2_def]
          simp only [hD_def] at hs
          field_simp
          nlinarith [hs]
        have hR12 : ∀ t, R1 t ≤ R2 t := by
          intro t
          simp only [hR1_def, hR2_def]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [Real.sqrt_nonneg (D t)]
        have hIcc : ∀ t, 0 ≤ D t → {z | M.X w z ≤ t} = Set.Icc (R1 t) (R2 t) := by
          intro t hDt
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_Icc, hX]
          have hf := hfac t z hDt
          constructor
          · intro h
            have hp : (z - R1 t) * (z - R2 t) ≤ 0 := by
              by_contra hc; push Not at hc
              have := mul_pos hγ hc; linarith
            by_contra hc
            rw [not_and_or] at hc
            rcases hc with hc | hc <;> push Not at hc
            · have := mul_pos_of_neg_of_neg (by linarith : z - R1 t < 0)
                (by linarith [hR12 t] : z - R2 t < 0)
              linarith
            · have := mul_pos (by linarith [hR12 t] : 0 < z - R1 t) (by linarith : 0 < z - R2 t)
              linarith
          · rintro ⟨h1, h2⟩
            have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ z - R1 t)
              (by linarith : z - R2 t ≤ 0)
            nlinarith [mul_nonpos_of_nonneg_of_nonpos hγ.le this]
        have hIoo : ∀ t, 0 ≤ D t → {z | M.X w z < t} = Set.Ioo (R1 t) (R2 t) := by
          intro t hDt
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_Ioo, hX]
          have hf := hfac t z hDt
          constructor
          · intro h
            have hp : (z - R1 t) * (z - R2 t) < 0 := by
              by_contra hc; push Not at hc
              have := mul_nonneg hγ.le hc; linarith
            by_contra hc
            rw [not_and_or] at hc
            rcases hc with hc | hc <;> push Not at hc
            · have := mul_nonneg_of_nonpos_of_nonpos (by linarith : z - R1 t ≤ 0)
                (by linarith [hR12 t] : z - R2 t ≤ 0)
              linarith
            · have := mul_nonneg (by linarith [hR12 t] : 0 ≤ z - R1 t) (by linarith : 0 ≤ z - R2 t)
              linarith
          · rintro ⟨h1, h2⟩
            have := mul_neg_of_pos_of_neg (by linarith : 0 < z - R1 t)
              (by linarith : z - R2 t < 0)
            nlinarith [mul_neg_of_pos_of_neg hγ this]
        -- measures of intervals
        have hint : ∀ u v, IntervalIntegrable φ volume u v := fun u v => hφc.intervalIntegrable u v
        have hmIcc : ∀ u v, u ≤ v → (gaussianReal 0 1 (Set.Icc u v)).toReal = Φ v - Φ u := by
          intro u v huv
          rw [gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
            (setIntegral_nonneg measurableSet_Icc (fun s _ => gaussianPDFReal_nonneg 0 1 s)),
            integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
            intervalIntegral.integral_interval_sub_left (hint 0 v) (hint 0 u)]
        have hmIoo : ∀ u v, u ≤ v → (gaussianReal 0 1 (Set.Ioo u v)).toReal = Φ v - Φ u := by
          intro u v huv
          rw [gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal
            (setIntegral_nonneg measurableSet_Ioo (fun s _ => gaussianPDFReal_nonneg 0 1 s)),
            ← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le huv,
            intervalIntegral.integral_interval_sub_left (hint 0 v) (hint 0 u)]
        -- Peps as difference
        have hδ : 0 < D x / (4 * a) := by positivity
        have hPeps : ∀ ε, 0 < ε → ε < D x / (4 * a) → Peps M x w ε = H (x + ε) - H (x - ε) := by
          intro ε hε0 hε1
          have hD1 : 0 ≤ D (x + ε) := by
            simp only [hD_def] at hDx ⊢; nlinarith
          have hD2 : 0 ≤ D (x - ε) := by
            have : 4 * a * ε < D x := by
              rw [lt_div_iff₀ (by positivity)] at hε1; linarith
            simp only [hD_def] at hDx this ⊢; nlinarith
          have hset : {z | |M.X w z - x| ≤ ε} = {z | M.X w z ≤ x + ε} \ {z | M.X w z < x - ε} := by
            ext z
            simp only [Set.mem_ofPred_eq, Set.mem_sdiff, abs_le, not_lt]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
            · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
          have hsub : {z | M.X w z < x - ε} ⊆ {z | M.X w z ≤ x + ε} := by
            intro z hz
            simp only [Set.mem_ofPred_eq] at hz ⊢
            linarith
          have hmeas : MeasurableSet {z | M.X w z < x - ε} := by
            rw [hIoo _ hD2]; exact measurableSet_Ioo
          unfold Peps
          rw [hset, ← measureReal_def, measureReal_sdiff hsub hmeas, measureReal_def, measureReal_def,
            hIcc _ hD1, hIoo _ hD2, hmIcc _ _ (hR12 _), hmIoo _ _ (hR12 _)]
        -- derivative
        have hsx : 0 < √(D x) := Real.sqrt_pos.mpr hDx
        have hDd : HasDerivAt D (4 * a) x := by
          have := ((hasDerivAt_id x).sub_const c).const_mul (4 * a)
          simpa [hD_def] using this.const_add (b ^ 2)
        have hS : HasDerivAt (fun t => √(D t)) (4 * a / (2 * √(D x))) x := hDd.sqrt hDx.ne'
        have hR2d : HasDerivAt R2 ((4 * a / (2 * √(D x))) / (2 * a)) x :=
          (hS.const_add (-b)).div_const (2 * a)
        have hR1d : HasDerivAt R1 (-(4 * a / (2 * √(D x))) / (2 * a)) x :=
          (hS.const_sub (-b)).div_const (2 * a)
        have hΦd : ∀ y, HasDerivAt Φ (φ y) y := fun y =>
          (hφc.integral_hasStrictDerivAt 0 y).hasDerivAt
        have hHd : HasDerivAt H (φ (R2 x) * ((4 * a / (2 * √(D x))) / (2 * a))
            - φ (R1 x) * (-(4 * a / (2 * √(D x))) / (2 * a))) x :=
          ((hΦd (R2 x)).comp x hR2d).sub ((hΦd (R1 x)).comp x hR1d)
        have hL : φ (R2 x) * ((4 * a / (2 * √(D x))) / (2 * a))
            - φ (R1 x) * (-(4 * a / (2 * √(D x))) / (2 * a)) = M.q1 w x + M.q2 w x := by
          have e1 : M.q1 w x = φ (R1 x) / √(D x) := by
            simp only [DeltaGamma.q1, if_pos hlt]; rfl
          have e2 : M.q2 w x = φ (R2 x) / √(D x) := by
            simp only [DeltaGamma.q2, if_pos hlt]; rfl
          rw [e1, e2]
          field_simp
          ring
        rw [← hL]
        set L := φ (R2 x) * ((4 * a / (2 * √(D x))) / (2 * a))
            - φ (R1 x) * (-(4 * a / (2 * √(D x))) / (2 * a))
        have h1 := hHd.tendsto_slope_zero_right
        have h2 := hHd.tendsto_slope_zero_left
        have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[<] 0) := by
          have := (continuous_neg.tendsto' (0:ℝ) 0 neg_zero)
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (this.mono_left nhdsWithin_le_nhds) ?_
          filter_upwards [self_mem_nhdsWithin] with ε hε
          simp only [Set.mem_Ioi] at hε
          simp only [Set.mem_Iio]; linarith
        have h3 := (h1.add (h2.comp hneg)).div_const 2
        rw [show (L + L) / 2 = L by ring] at h3
        refine h3.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
        rw [hPeps ε hε.1 hε.2]
        simp only [Function.comp, smul_eq_mul]
        have : ε ≠ 0 := hε.1.ne'
        rw [← sub_eq_add_neg]
        field_simp
        ring
      · have hq1 : M.q1 w x = 0 := by simp [DeltaGamma.q1, not_lt.mpr hgt.le]
        have hq2 : M.q2 w x = 0 := by simp [DeltaGamma.q2, not_lt.mpr hgt.le]
        rw [hq1, hq2, add_zero]
        apply tendsto_const_nhds.congr'
        have hpos : (0:ℝ) < M.gStar w - x := by linarith
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        have hempty : {z | |M.X w z - x| ≤ ε} = ∅ := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have := hXg z
          have h2 := hε.2
          rw [abs_of_pos (by linarith)]
          linarith
        simp [Peps, hempty]
