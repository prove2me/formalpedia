-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_BV_local_C1_postpayment_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:52:01.006785+00:00
-- url     : https://prove2.me/submissions/37ad0ba9-8c7d-4747-8d5c-49adf66877cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (cap lo hi : ℝ)
    (hlr : lo < hi) (hsub : Icc lo hi ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈ Icc lo hi) →
      BoundedVariationOn
        (fun t : ℝ≥0 =>
          w (x + X.X (min t T) ω - rightLimit D (min t T) ω))
        Set.univ := by
  obtain ⟨L, hL, hLip⟩ :=
    avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
      X hBV w cap lo hi hlr hsub (fun _ => hwC1)
  let K : NNReal := ⟨L, hL⟩
  have hwLip : LipschitzOnWith K w (Icc lo hi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have hK : (K : ℝ) = L := rfl
    simpa only [Real.dist_eq, hK] using hLip a ha b hb
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T hstay
  let Y : ℝ≥0 → ℝ := fun t =>
    x + X.X (min t T) ω - rightLimit D (min t T) ω
  have hMap : MapsTo Y Set.univ (Icc lo hi) := by
    intro t ht
    exact hstay t
  have hY : BoundedVariationOn Y Set.univ := hω T
  simpa only [Y, Function.comp_def] using
    (hwLip.comp_boundedVariationOn hMap hY)
