-- Prove2me | solution 1 for AvramDividend.Classical.avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:16:17.996625+00:00
-- url     : https://prove2.me/submissions/10c73246-e464-4854-b014-9d126c2a4f1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) = 0} =
      P {ω : Ω | K ω = 0} := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} =
    P {ω : Ω | K ω = 0}
  have hAE : ∀ᵐ ω ∂P, (NX ω (Ioc 0 T ×ˢ B) = 0 ↔ K ω = 0) := by
    filter_upwards [
      avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
        X hFinite T B hB hNeg K hK hCount] with ω hω
    obtain ⟨S, hS, hKω⟩ := hω
    have hCard :=
      avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
        X ω T B hB S hS 0 T bot_le le_rfl
    have hFilter : S.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ T) = S := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · intro hu
        exact hu.1
      · intro hu
        have hs := (hS u).mp hu
        exact ⟨hu, hs.1, hs.2.1⟩
    change NX ω (Ioc 0 T ×ˢ B) = 0 ↔ K ω = 0
    rw [hCard, hFilter, hKω]
    simp
  have hEq : (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B) = 0) =ᵐ[P]
      (fun ω : Ω => K ω = 0) := by
    filter_upwards [hAE] with ω hω
    exact propext hω
  exact measure_congr hEq
