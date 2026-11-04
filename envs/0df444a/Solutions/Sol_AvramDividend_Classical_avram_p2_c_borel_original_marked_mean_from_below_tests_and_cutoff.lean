-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_from_below_tests_and_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:00:59.682283+00:00
-- url     : https://prove2.me/submissions/53e1ebf8-141c-42a4-bedf-dc0dad28c8c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Below-cutoff dense tests plus the cutoff mass identify the original marked Borel measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hCut : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) = ρ (Iic (-ε)))
    (hBelow : ∀ a : ℝ, a ∈ D → a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic a) ∂P) = ρ (Iic a))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by
  have hDenseTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
      ρ (Iic a ∩ Iic (-ε)) := by
    intro a ha
    by_cases hac : a < -ε
    · have hSmall : Iic a ∩ Iic (-ε) = Iic a := by
        ext x
        simp only [mem_inter_iff, mem_Iic]
        constructor
        · exact And.left
        · intro hxa
          exact ⟨hxa, le_trans hxa (le_of_lt hac)⟩
      simpa only [hSmall] using hBelow a ha hac
    · have hBig : Iic a ∩ Iic (-ε) = Iic (-ε) := by
        ext x
        simp only [mem_inter_iff, mem_Iic]
        constructor
        · exact And.right
        · intro hxc
          exact ⟨le_trans hxc (le_of_not_gt hac), hxc⟩
      simpa only [hBig] using hCut
  exact avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
    X s t hst ε hε ρ hρfin D hDense hDenseTests B hB
