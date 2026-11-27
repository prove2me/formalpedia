-- Prove2me | solution 1 for DataDrivenRO.Guarantee.Supplement.theorem_12_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:30.994401+00:00
-- url     : https://prove2.me/submissions/c40c6685-833a-4e17-be7a-4bdefa00ffb0

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Supplement_DY

open MeasureTheory
open scoped ENNReal

open DataDrivenRO
open DataDrivenRO.Guarantee
open DataDrivenRO.Guarantee.Supplement

/-- Under the brief's norm convention sqrt(xᵀMx), the printed SDP of Theorem 12
has a feasible value strictly smaller than both a point of (36) and an admissible VaR.
All moment data are nondegenerate and the empirical law is in the confidence region. -/
theorem solution :
    let lo : Fin 1 → ℝ := fun _ => -2
    let hi : Fin 1 → ℝ := fun _ => 2
    let mu : Fin 1 → ℝ := fun _ => 0
    let Sigma : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 4)
    let C : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 1 / 2)
    let S : Fin 2 → (Fin 1 → ℝ) := fun j _ => if j = 0 then -2 else 2
    let Phat : Measure (Fin 1 → ℝ) :=
      (1 / 2 : ℝ≥0∞) • Measure.dirac (S 0) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (S 1)
    let P : Measure (Fin 1 → ℝ) := Measure.dirac (fun _ => (1 / 2 : ℝ))
    let U := UDY lo hi mu Sigma C (1 / 16) 1 (999 / 1000)
    Sigma.PosDef ∧ C.transpose * C = Sigma⁻¹ ∧
    (∀ i, (∑ j, S j i) / 2 = mu i) ∧
    (∀ i j, (∑ k, (S k i - mu i) * (S k j - mu j)) / 2 = Sigma i j) ∧
    Phat ∈ regionDY lo hi mu Sigma (1 / 16) 1 ∧
    P ∈ regionDY lo hi mu Sigma (1 / 16) 1 ∧
    (fun _ => (1 / 2 : ℝ)) ∈ U ∧ U.Nonempty ∧ IsCompact U ∧ Convex ℝ U ∧
    (1 / 2 : ℝ) ≤ RobustMDP.Shared.supportFunction U (fun _ => 1) ∧
    DataDrivenRO.Guarantee.VaR P (999 / 1000) (fun _ => 1) = 1 / 2 ∧
    (190 / 999 : ℝ) ∈ sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1) ∧
    (190 / 999 : ℝ) < 1 / 2 ∧
    ¬ IsGLB (sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1))
      (RobustMDP.Shared.supportFunction U (fun _ => 1)) ∧
    ¬ IsGLB (sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1))
      (sSup ((fun Q : Measure (Fin 1 → ℝ) =>
        DataDrivenRO.Guarantee.VaR Q (999 / 1000) (fun _ => 1)) ''
        regionDY lo hi mu Sigma (1 / 16) 1)) := by
          intro lo hi mu Sigma C S Phat P U
          -- 1x1 PSD
          have hpsd1 : ∀ M : Matrix (Fin 1) (Fin 1) ℝ, 0 ≤ M 0 0 → M.PosSemidef := by
            intro M hM
            refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
            · ext i j
              fin_cases i; fin_cases j; simp [Matrix.conjTranspose]
            · intro x
              simp [dotProduct, Matrix.mulVec]
              nlinarith [mul_nonneg hM (mul_self_nonneg (x 0))]
          have hblock : ∀ (s : ℝ) (x : Fin 1 → ℝ) (A : Matrix (Fin 1) (Fin 1) ℝ),
              0 ≤ s → 0 ≤ A 0 0 → x 0 ^ 2 ≤ s * A 0 0 → (momentBlock s x A).PosSemidef := by
            intro s x A hs hA hx
            refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
            · ext i j
              rcases i with i | i <;> rcases j with j | j <;>
                simp [Matrix.conjTranspose, momentBlock, Subsingleton.elim i 0, Subsingleton.elim j 0]
              all_goals rfl
            · intro y
              have key : 0 ≤ s * y (Sum.inl ()) ^ 2 + 2 * x 0 * y (Sum.inl ()) * y (Sum.inr 0)
                  + A 0 0 * y (Sum.inr 0) ^ 2 := by
                generalize y (Sum.inl ()) = a
                generalize y (Sum.inr 0) = b
                rcases hs.eq_or_lt with h0 | h0
                · have : x 0 = 0 := by
                    rw [← h0] at hx
                    nlinarith [sq_nonneg (x 0), pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm (by linarith : x 0 ^ 2 ≤ 0) (sq_nonneg _))]
                  rw [this, ← h0]
                  nlinarith [mul_nonneg hA (sq_nonneg b)]
                · have h1 : 0 ≤ s * (s * a ^ 2 + 2 * x 0 * a * b + A 0 0 * b ^ 2) := by
                    nlinarith [sq_nonneg (s * a + x 0 * b), mul_nonneg (sub_nonneg.2 hx) (sq_nonneg b)]
                  exact nonneg_of_mul_nonneg_right h1 h0
              simp [dotProduct, Matrix.mulVec, momentBlock, Fintype.sum_sum_type, Matrix.fromBlocks]
              nlinarith [key]
          have hSinv : Sigma⁻¹ = Matrix.of (fun _ _ => (1 / 4 : ℝ)) := by
            apply Matrix.inv_eq_right_inv
            ext i j
            fin_cases i; fin_cases j
            simp [Sigma, Matrix.mul_apply]
          have hsq : Real.sqrt (1 / 16) = 1 / 4 := by
            rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num]
            exact Real.sqrt_sq (by norm_num)
          have hPD : Sigma.PosDef := by
            refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
            · ext i j
              simp [Sigma]
            · intro x hx
              have hx0 : x 0 ≠ 0 := by
                intro h
                apply hx
                ext i
                rw [Subsingleton.elim i 0, h]; rfl
              simp [dotProduct, Matrix.mulVec, Sigma]
              have := mul_self_pos.2 hx0
              nlinarith
          have hCC : C.transpose * C = Sigma⁻¹ := by
            rw [hSinv]
            ext i j
            simp [C, Matrix.mul_apply]
            norm_num
          have hmean : ∀ i, (∑ j, S j i) / 2 = mu i := by
            intro i
            simp [S, mu, Fin.sum_univ_two]
          have hcov : ∀ i j, (∑ k, (S k i - mu i) * (S k j - mu j)) / 2 = Sigma i j := by
            intro i j
            simp [S, mu, Sigma, Fin.sum_univ_two]
            norm_num
          have hregion : ∀ Q : Measure (Fin 1 → ℝ), IsProbabilityMeasure Q → Q (box lo hi)ᶜ = 0 →
              (∫ u, u 0 ∂Q) ^ 2 ≤ 1 / 4 → (∫ u, u 0 * u 0 ∂Q) ≤ 4 →
              Q ∈ regionDY lo hi mu Sigma (1 / 16) 1 := by
            intro Q h1 h2 h3 h4
            refine ⟨h1, h2, ?_, ?_⟩
            · rw [hSinv]
              simp [dotProduct, Matrix.mulVec, mu]
              nlinarith
            · apply hpsd1
              simp [Sigma, mu]
              exact h4
          have hPhat : Phat ∈ regionDY lo hi mu Sigma (1 / 16) 1 := by
            have hint : ∀ f : (Fin 1 → ℝ) → ℝ, (∫ u, f u ∂Phat) = (f (S 0) + f (S 1)) / 2 := by
              intro f
              have hi1 : ∀ a : Fin 1 → ℝ, Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac a) := by
                intro a
                apply Integrable.smul_measure _ (by simp)
                exact integrable_dirac (by simp)
              rw [integral_add_measure (hi1 _) (hi1 _), integral_smul_measure, integral_smul_measure,
                integral_dirac, integral_dirac]
              simp
              ring
            have hS : ∀ j, S j ∈ box lo hi := by
              intro j i
              fin_cases j <;> simp [S, lo, hi]
            apply hregion
            · constructor
              simp [Phat]
              exact ENNReal.inv_two_add_inv_two
            · simp [Phat, hS]
            · rw [hint]
              simp [S]
            · rw [hint]
              simp [S]
              norm_num
          have hP : P ∈ regionDY lo hi mu Sigma (1 / 16) 1 := by
            apply hregion
            · infer_instance
            · have : (fun _ => (1 / 2 : ℝ)) ∈ box lo hi := by
                intro i
                norm_num [lo, hi]
              simp only [P]
              rw [Measure.dirac_apply]
              simpa using this
            · simp only [P]
              rw [integral_dirac]
              norm_num
            · simp only [P]
              rw [integral_dirac]
              norm_num
          have hU : U = Set.Icc (fun _ => -(502 / 999 : ℝ)) (fun _ => (502 / 999 : ℝ)) := by
            ext u
            constructor
            · rintro ⟨_, lam, w, m, A, Ah, _, _, hlam, hm, _, _, heq, hw, _⟩
              have e := congrFun heq 0
              have hm0 := hm 0
              rw [hsq] at hw
              have hwsq : (C.mulVec w ⬝ᵥ C.mulVec w) = (w 0 / 2) ^ 2 := by
                simp [C, dotProduct, Matrix.mulVec]
                ring
              rw [hwsq, Real.sqrt_sq_eq_abs, abs_le] at hw
              simp [mu] at e
              simp only [lo, hi] at hm0
              norm_num at hlam
              rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
              constructor
              · intro i
                rw [Subsingleton.elim i 0]
                linarith [hw.1, hw.2, hm0.1, hm0.2]
              · intro i
                rw [Subsingleton.elim i 0]
                linarith [hw.1, hw.2, hm0.1, hm0.2]
            · intro hu
              have h1 : -(502 / 999 : ℝ) ≤ u 0 := hu.1 0
              have h2 : u 0 ≤ (502 / 999 : ℝ) := hu.2 0
              refine ⟨?_, 1000 / 999, fun _ => -(500 / 502) * u 0, fun _ => -(2 / 502) * u 0,
                Matrix.of (fun _ _ => 4 / 999), Matrix.of (fun _ _ => 4), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro i
                rw [Subsingleton.elim i 0]
                simp only [lo, hi]
                constructor <;> linarith
              · exact hpsd1 _ (by norm_num)
              · exact hpsd1 _ (by norm_num)
              · norm_num
              · intro i
                simp only [lo, hi]
                constructor <;> linarith
              · apply hblock
                · norm_num
                · norm_num
                · norm_num
                  nlinarith
              · apply hblock
                · norm_num
                · norm_num
                · norm_num
                  nlinarith
              · ext i
                rw [Subsingleton.elim i 0]
                simp [mu]
                ring
              · rw [hsq]
                have hwsq : (C.mulVec (fun _ => -(500 / 502) * u 0) ⬝ᵥ C.mulVec (fun _ => -(500 / 502) * u 0)) = ((-(500 / 502) * u 0) / 2) ^ 2 := by
                  simp [C, dotProduct, Matrix.mulVec]
                  ring
                rw [hwsq, Real.sqrt_sq_eq_abs, abs_le]
                constructor <;> linarith
              · apply hpsd1
                simp [Sigma, mu, Matrix.vecMulVec_apply]
                norm_num
          have hmem : (fun _ => (1 / 2 : ℝ)) ∈ U := by
            rw [hU]
            constructor <;> intro i <;> norm_num
          have hcomp : IsCompact U := by rw [hU]; exact isCompact_Icc
          have hconv : Convex ℝ U := by rw [hU]; exact convex_Icc _ _
          have hsupp : (1 / 2 : ℝ) ≤ RobustMDP.Shared.supportFunction U (fun _ => 1) := by
            refine le_csSup ?_ ⟨_, hmem, by simp⟩
            refine ⟨502 / 999, ?_⟩
            rintro _ ⟨u, hu, rfl⟩
            rw [hU] at hu
            simpa using hu.2 0
          have hVaR : DataDrivenRO.Guarantee.VaR P (999 / 1000) (fun _ => 1) = 1 / 2 := by
            unfold DataDrivenRO.Guarantee.VaR MultistageStochastic.valueAtRisk
            have : {y : ℝ | ENNReal.ofReal (1 - 999 / 1000) ≤ P {ω | ω ⬝ᵥ (fun _ => (1:ℝ)) ≤ y}} = Set.Ici (1 / 2) := by
              ext y
              simp only [P, Set.mem_ofPred_eq, Set.mem_Ici]
              rw [Measure.dirac_apply]
              by_cases hy : (1 / 2 : ℝ) ≤ y
              · rw [Set.indicator_of_mem (by simpa [dotProduct] using hy)]
                simp only [hy, iff_true, Pi.one_apply]
                rw [ENNReal.ofReal_le_one]
                norm_num
              · rw [Set.indicator_of_notMem (by simpa [dotProduct] using hy)]
                simp only [hy, iff_false]
                simp
                norm_num
            rw [this, csInf_Ici]
          have hsdp : (190 / 999 : ℝ) ∈ sdpPrinted lo hi mu Sigma (1 / 16) 1 (999 / 1000) (fun _ => 1) := by
            refine ⟨2, 1 / 8, 2125 / 999, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, 0,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact Matrix.isHermitian_zero
            · norm_num
            · intro i; norm_num
            · norm_num
            · apply hblock
              · simp [dotProduct, lo, hi]
              · simp
              · simp
            · apply hblock
              · simp [dotProduct, lo, hi]
                norm_num
              · simp
              · simp
            · rw [hsq, hSinv]
              have : weightedNorm (Matrix.of (fun _ _ => (1 / 4 : ℝ))) ((fun _ => (1:ℝ)) + 2 • (0 : Matrix (Fin 1) (Fin 1) ℝ).mulVec mu) = 1 / 2 := by
                unfold weightedNorm
                simp [dotProduct, Matrix.mulVec]
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
                exact Real.sqrt_sq (by norm_num)
              rw [this]
              simp [dotProduct, mu]
              norm_num
          have hlt : (190 / 999 : ℝ) < 1 / 2 := by norm_num
          have hsup2 : (1 / 2 : ℝ) ≤ (sSup ((fun Q : Measure (Fin 1 → ℝ) =>
                DataDrivenRO.Guarantee.VaR Q (999 / 1000) (fun _ => 1)) ''
                regionDY lo hi mu Sigma (1 / 16) 1)) := by
            refine le_csSup ?_ ⟨P, hP, hVaR⟩
            refine ⟨2, ?_⟩
            rintro _ ⟨Q, hQ, rfl⟩
            obtain ⟨hQp, hQb, _⟩ := hQ
            have hae : ∀ᵐ u ∂Q, u ∈ box lo hi := by
              rw [ae_iff]
              exact hQb
            simp only [DataDrivenRO.Guarantee.VaR, MultistageStochastic.valueAtRisk]
            apply csInf_le
            · refine ⟨-2, ?_⟩
              intro y hy
              by_contra hlt2
              rw [not_le] at hlt2
              have h0 : Q {ω | ω ⬝ᵥ (fun _ => (1:ℝ)) ≤ y} = 0 := by
                refine measure_mono_null ?_ hQb
                intro u hu hbox
                have a := (hbox 0).1
                simp [dotProduct] at hu
                simp only [lo] at a
                linarith
              rw [Set.mem_ofPred_eq, h0] at hy
              simp at hy
              norm_num at hy
            · rw [Set.mem_ofPred_eq]
              have h1 : Q {ω | ω ⬝ᵥ (fun _ => (1:ℝ)) ≤ 2} = 1 := by
                rw [← prob_compl_eq_zero_iff₀]
                · refine measure_mono_null ?_ hQb
                  intro u hu hbox
                  apply hu
                  have a := (hbox 0).2
                  simp [dotProduct]
                  exact a
                · apply MeasurableSet.nullMeasurableSet
                  apply measurableSet_le
                  · simp only [dotProduct]
                    fun_prop
                  · fun_prop
              rw [h1, ENNReal.ofReal_le_one]
              norm_num
          refine ⟨hPD, hCC, hmean, hcov, hPhat, hP, hmem, ⟨_, hmem⟩, hcomp, hconv, hsupp, hVaR, hsdp, hlt, ?_, ?_⟩
          · intro h
            have := h.1 hsdp
            linarith
          · intro h
            have := h.1 hsdp
            linarith
