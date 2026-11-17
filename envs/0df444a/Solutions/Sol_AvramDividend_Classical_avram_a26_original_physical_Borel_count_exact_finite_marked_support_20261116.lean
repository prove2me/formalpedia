-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:08:08.78432+00:00
-- url     : https://prove2.me/submissions/ea3d39a1-7c6a-4d3e-97a8-8f232af177dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_marked_times_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
    ∀ᵐ ω ∂P,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B) ∧
        K ω = S.card := by
  classical
  have hSupport :=
    avram_a20_original_borel_physical_marked_times_finite_ae
      X hFinite T B hB hNeg
  filter_upwards [hSupport, hCount] with ω hS hCountω
  let S : Finset ℝ≥0 := hS.toFinset
  refine ⟨S, ?_, ?_⟩
  · intro u
    simp [S]
  · have hFilter : (hS.toFinset.filter
        (fun u : ℝ≥0 => 0 < u ∧ u ≤ T)) = hS.toFinset := by
      ext u
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · exact And.left
      · intro h
        exact ⟨h, ⟨h.1, h.2.1⟩⟩
    have hCard := avram_a20_original_borel_window_finite_marked_times_card
      X ω T B hB 0 T (by exact bot_le) (le_refl _) hS
    have hToReal := congrArg ENNReal.toReal hCard
    have hResult : (K ω : ℝ) = (S.card : ℝ) := by
      rw [hCountω]
      simpa only [hFilter, S, ENNReal.toReal_natCast] using hToReal
    exact_mod_cast hResult
