-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:27:41.326257+00:00
-- url     : https://prove2.me/submissions/18d29ed3-2b8c-4055-b1b1-bd7e670002d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Dense original count tests imply the finite cutoff mean and every Borel mark identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = ρ (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by
  obtain ⟨q, hStrict, hMem, hTend⟩ :=
    hDense.exists_seq_strictAnti_tendsto (-ε)
  have hqLarge : -ε ≤ q 0 := le_of_lt (hMem 0).1
  have hqD : q 0 ∈ D := (hMem 0).2
  have hBig : Iic (q 0) ∩ Iic (-ε) = Iic (-ε) := by
    ext x
    simp only [mem_inter_iff, mem_Iic]
    constructor
    · exact And.right
    · intro hx
      exact ⟨le_trans hx hqLarge, hx⟩
  have hρlt : ρ (Iic (-ε)) < ⊤ := lt_top_iff_ne_top.mpr hρfin
  have hFiniteMean : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ := by
    calc
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic (q 0) ∩ Iic (-ε))) ∂P) := by rw [hBig]
      _ = ρ (Iic (q 0) ∩ Iic (-ε)) := hTests (q 0) hqD
      _ = ρ (Iic (-ε)) := by rw [hBig]
      _ < ⊤ := hρlt
  exact avram_p2_c_borel_original_marked_mean_ext_of_dense_tests
    X s t hst ε hε hFiniteMean ρ hρfin D hDense hTests B hB
