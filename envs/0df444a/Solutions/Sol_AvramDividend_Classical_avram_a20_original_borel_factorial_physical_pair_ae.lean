-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_factorial_physical_pair_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:19:37.690104+00:00
-- url     : https://prove2.me/submissions/dfde62ed-93e8-4c21-b87a-7bc0f88612d8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_linear_ordered_set_factorial_pair_ncard
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    ∀ᵐ ω ∂P, (N ω).toReal * ((N ω).toReal - 1) =
      2 * ((((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard) : ℝ) := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
    0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  change ∀ᵐ ω ∂P,
    (N ω).toReal * ((N ω).toReal - 1) =
      2 * ((((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard) : ℝ)
  have hν : X.ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hFin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) B hB hν
    simpa only [tsub_zero, N] using
      (avram_ja34_original_all_negative_borel_expected_count_exact X T B hB hNeg)
  filter_upwards [hFin] with ω hω
  have hCount : N ω = ((S ω).encard : ℝ≥0∞) := by
    simpa only [N, S] using
      (avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω 0 T B hB)
  have hSetFin : (S ω).Finite := by
    apply Set.encard_lt_top_iff.mp
    have hE : ((S ω).encard : ℝ≥0∞) < ⊤ := by
      simpa only [hCount] using hω
    exact_mod_cast hE
  have hRealCount : (N ω).toReal = ((S ω).ncard : ℝ) := by
    rw [hCount, hSetFin.encard_eq_coe_toFinset_card,
      Set.ncard_eq_toFinset_card (S ω) hSetFin]
    simp
  rw [hRealCount]
  exact avram_a20_finite_linear_ordered_set_factorial_pair_ncard
    (S ω) hSetFin
