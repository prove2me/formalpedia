-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_nat_count_realisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:06:55.838826+00:00
-- url     : https://prove2.me/submissions/571b4034-da9f-4b4e-9fad-6614d4db3672

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
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
    ∃ K : Ω → ℕ,
      Measurable K ∧
      ∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change ∃ K : Ω → ℕ, Measurable K ∧
      ∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal
  let K : Ω → ℕ := fun ω => Nat.floor (N ω).toReal
  have hMeas : Measurable N := by
    simpa only [N, zero_add] using
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable X 0 T B hB)
  have hν : X.ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hFin : ∀ᵐ ω ∂P, N ω < ⊤ := by
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) B hB hν
    simpa only [tsub_zero, N] using
      (avram_ja34_original_all_negative_borel_expected_count_exact X T B hB hNeg)
  refine ⟨K, hMeas.ennreal_toReal.nat_floor, ?_⟩
  filter_upwards [hFin] with ω hω
  let S : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  have hCount : N ω = (S.encard : ℝ≥0∞) := by
    simpa only [N, S] using
      (avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard X ω 0 T B hB)
  have hSetFin : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    have hE : (S.encard : ℝ≥0∞) < ⊤ := by
      simpa only [hCount] using hω
    exact_mod_cast hE
  obtain ⟨n, hn⟩ := hSetFin.exists_encard_eq_coe
  have hN : N ω = (n : ℝ≥0∞) := by
    rw [hCount, hn]
    simp
  change ((Nat.floor (N ω).toReal : ℕ) : ℝ) = (N ω).toReal
  rw [hN]
  simp only [ENNReal.toReal_natCast, Nat.floor_natCast]
