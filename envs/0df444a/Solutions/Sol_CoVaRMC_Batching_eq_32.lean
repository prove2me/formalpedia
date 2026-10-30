-- Prove2me | solution 1 for CoVaRMC.Batching.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:29:26.481145+00:00
-- url     : https://prove2.me/submissions/bdb88db5-7eaa-4e23-9daa-00b993fb8544

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_CoVaRMC_Batching_lemma_3
import Theorems.Thm_CoVaRMC_Batching_cond_density
import Theorems.Thm_CoVaRMC_Batching_eq_30

open MeasureTheory ProbabilityTheory Filter Topology

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop)
    (t : ℝ) :
    ∃ (g : ℕ → ℝ) (C : ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ ν in atTop, |cmk P S α β c (Aconst D β v c) t (k ν) (m ν) + t - g ν| ≤ C * √(k ν : ℝ) / m ν := by
  have hA1' := hA1
  obtain ⟨h𝒳o, hv𝒳, h𝒴o, hc𝒴, -, -, -, -, -⟩ := hA1'
  have hcd := CoVaRMC.Batching.cond_density D Fc v c 𝒳 𝒴 hFc hA1 v hv𝒳 c hc𝒴
  set f := D.condDensity c v with hfdef
  set A := Aconst D β v c with hAdef
  set σ0 := √(β * (1 - β)) with hσ0
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.mpr (mul_pos hβ.1 (by linarith [hβ.2]))
  have hApos : 0 < A := by
    simp only [hAdef, Aconst]
    exact div_pos hσ0pos hcd.2
  have hAf : A * f = σ0 := by
    simp only [hAdef, Aconst, ← hfdef, ← hσ0]; field_simp [hcd.2.ne']
  obtain ⟨-, -, hσlim⟩ := CoVaRMC.Batching.eq_30 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
    P S hSm hSi hSl k m hk0 hm0 hk hm t
  set σ : ℕ → ℝ := fun ν => sigmaHat P S α (m ν) (yk c A t (k ν)) with hσdef
  set F : ℕ → ℝ := fun ν => Fc (yk c A t (k ν)) v with hFdef
  set p : ℕ → ℝ := fun ν => pHat P S α (m ν) (yk c A t (k ν)) with hpdef
  have hsk : Tendsto (fun ν => √(k ν : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  have hskpos : ∀ ν, 0 < √(k ν : ℝ) := fun ν => Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)
  -- `√k (F(y_k|v) - β) → t A f`
  have hlin : Tendsto (fun ν => √(k ν : ℝ) * (F ν - β)) atTop (𝓝 (t * A * f)) := by
    by_cases ht : t = 0
    · simp only [hFdef, yk, ht, zero_mul, zero_div, add_zero, hc, sub_self, mul_zero]
      exact tendsto_const_nhds
    set h : ℕ → ℝ := fun ν => t * A / √(k ν : ℝ) with hhdef
    have hh0 : Tendsto h atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact hsk.const_div_atTop _
      · exact Eventually.of_forall fun ν => div_ne_zero (mul_ne_zero ht hApos.ne') (hskpos ν).ne'
    have hslope := (hasDerivAt_iff_tendsto_slope_zero.mp hcd.1).comp hh0
    have heq : ∀ ν, √(k ν : ℝ) * (F ν - β) =
        (t * A) * ((h ν)⁻¹ • (Fc (c + h ν) v - Fc c v)) := by
      intro ν
      simp only [hFdef, hhdef, yk, hc, smul_eq_mul]
      field_simp [(hskpos ν).ne', ht, hApos.ne']
    simp_rw [heq]
    exact hslope.const_mul _
  set g : ℕ → ℝ := fun ν => √(k ν : ℝ) / σ ν * (β - F ν) + t with hgdef
  refine ⟨g, 2 * |(Classical.choose (CoVaRMC.Batching.lemma_3 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M
      hM hM1 hM2 P S hSm hSi hSl))| / σ0, ?_, ?_⟩
  · have : Tendsto g atTop (𝓝 (-(1 / σ0) * (t * A * f) + t)) := by
      have h1 : Tendsto (fun ν => -(1 / σ ν) * (√(k ν : ℝ) * (F ν - β)) + t) atTop
          (𝓝 (-(1 / σ0) * (t * A * f) + t)) :=
        (((tendsto_const_nhds.div hσlim hσ0pos.ne').neg).mul hlin).add tendsto_const_nhds
      refine h1.congr (fun ν => ?_)
      simp only [hgdef]; ring
    have h0 : -(1 / σ0) * (t * A * f) + t = 0 := by
      rw [mul_assoc t, hAf]; field_simp; ring
    rwa [h0] at this
  · have hC := Classical.choose_spec (CoVaRMC.Batching.lemma_3 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M
      hM hM1 hM2 P S hSm hSi hSl)
    set C := Classical.choose (CoVaRMC.Batching.lemma_3 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M
      hM hM1 hM2 P S hSm hSi hSl)
    have hyk : Tendsto (fun ν => yk c A t (k ν)) atTop (𝓝 c) := by
      simp only [yk]
      simpa using (hsk.const_div_atTop (t * A)).const_add c
    have hev1 : ∀ᶠ ν in atTop, ∀ y ∈ 𝒴, |pHat P S α (m ν) y - Fc y v| ≤ C / m ν :=
      hm.eventually hC
    have hev2 : ∀ᶠ ν in atTop, yk c A t (k ν) ∈ 𝒴 := hyk.eventually (h𝒴o.mem_nhds hc𝒴)
    have hev3 : ∀ᶠ ν in atTop, σ0 / 2 < σ ν :=
      hσlim.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev1, hev2, hev3] with ν h1 h2 h3
    have hb := h1 _ h2
    have hσpos : 0 < σ ν := by linarith
    have hmpos : (0 : ℝ) < m ν := by exact_mod_cast hm0 ν
    have hcm : cmk P S α β c A t (k ν) (m ν) = √(k ν : ℝ) / σ ν * (β - p ν) := rfl
    rw [hcm]
    have hrw : √(k ν : ℝ) / σ ν * (β - p ν) + t - g ν = √(k ν : ℝ) / σ ν * (F ν - p ν) := by
      simp only [hgdef]; ring
    rw [hrw, abs_mul, abs_of_pos (div_pos (hskpos ν) hσpos), abs_sub_comm]
    have hb' : |p ν - F ν| ≤ |C| / m ν :=
      hb.trans (div_le_div_of_nonneg_right (le_abs_self C) hmpos.le)
    calc √(k ν : ℝ) / σ ν * |p ν - F ν| ≤ √(k ν : ℝ) / σ ν * (|C| / m ν) :=
          mul_le_mul_of_nonneg_left hb' (div_pos (hskpos ν) hσpos).le
      _ ≤ √(k ν : ℝ) / (σ0 / 2) * (|C| / m ν) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (abs_nonneg _) hmpos.le)
          exact div_le_div_of_nonneg_left (hskpos ν).le (by linarith) h3.le
      _ = 2 * |C| / σ0 * √(k ν : ℝ) / m ν := by field_simp
