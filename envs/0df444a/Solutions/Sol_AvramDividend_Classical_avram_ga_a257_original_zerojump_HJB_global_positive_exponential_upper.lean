-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:16:08.495115+00:00
-- url     : https://prove2.me/submissions/014f60f2-b181-47d3-8c07-e56feb1e40d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
import Theorems.Thm_AvramDividend_Classical_avram_gledger64_topcap_C2_supplies_original_classical_derivatives
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_hjb_to_gaussian_pde
import Theorems.Thm_AvramDividend_Classical_avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → w y ≤ K * Real.exp (θ * y) := by
  have hsmooth :=
    avram_gledger64_topcap_C2_supplies_original_classical_derivatives
      w C hTopCap hw_smooth
  have hgen (y : ℝ) (hy : 0 < y) :
      X.σ^2/2*iteratedDeriv 2 w y +
        X.c*deriv w y-q*w y ≤ 0 := by
    have hPDE :=
      avram_p4_f11_zero_jump_hjb_to_gaussian_pde
        X hν q w C (fun z hz hzc => (hw_gen z hz hzc).2)
    exact hPDE y hy (by simp [hTopCap])
  have hσpos : 0 < |X.σ| := abs_pos.mpr hσ
  have hgen' (y : ℝ) (hy : 0 < y) :
      (|X.σ|)^2/2*iteratedDeriv 2 w y+
        X.c*deriv w y-q*w y ≤ 0 := by
    simpa only [sq_abs] using hgen y hy
  obtain ⟨Knear,hKnear,hNear⟩ :=
    avram_ga_a256_scalar_gaussian_HJB_positive_origin_upper
      |X.σ| X.c q 1 hσpos hq (by norm_num) w hsmooth hgen'
  obtain ⟨θ,Kfar,hθ,hKfar,hFar⟩ :=
    avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
      X hν hσ q hq w C hTopCap hw_smooth hw_gen 1 (by norm_num)
  let K := max Knear Kfar
  have hK : 0 ≤ K := le_trans hKnear (le_max_left _ _)
  refine ⟨θ,K,hθ,hK,?_⟩
  intro y hy
  have hExp : 1 ≤ Real.exp (θ*y) := by
    simpa using (Real.one_le_exp_iff.mpr (mul_nonneg hθ hy.le))
  rcases le_total y 1 with hSmall | hLarge
  · have hNearY := hNear y hy hSmall
    calc
      w y ≤ Knear := hNearY
      _ ≤ K := le_max_left _ _
      _ = K*1 := by ring
      _ ≤ K*Real.exp (θ*y) :=
        mul_le_mul_of_nonneg_left hExp hK
  · calc
      w y ≤ Kfar*Real.exp (θ*y) := hFar y hLarge
      _ ≤ K*Real.exp (θ*y) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
