-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_mapped_positive_clock_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:49:42.789729+00:00
-- url     : https://prove2.me/submissions/214a92c7-ad15-403f-98fe-aedc4cf62e5a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (m : Measure ℝ≥0) (s : Set ℝ≥0) (j : ℝ≥0 → ℝ) (F : ℝ≥0 × ℝ → ℝ)
    (hs : s ⊆ Ioi 0) (hF : ∀ p, p.1 ≠ 0 → F p = 0) :
    (∫ p, F p ∂((m.restrict s).map (fun u => (u, j u)))) = 0 := by
  classical
  by_cases hf : AEMeasurable (fun u => (u, j u)) (m.restrict s)
  · have h0s : (0 : ℝ≥0) ∉ s := fun h => (lt_irrefl (0 : ℝ≥0)) (hs h)
    have hmass : ((m.restrict s).map (fun u => (u, j u)))
        (Prod.fst ⁻¹' ({0} : Set ℝ≥0)) = 0 := by
      rw [Measure.map_apply_of_aemeasurable hf
        ((measurableSet_singleton (0 : ℝ≥0)).preimage measurable_fst)]
      change (m.restrict s) {0} = 0
      rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ≥0))]
      simp [h0s]
    have ha : ∀ᵐ p ∂((m.restrict s).map (fun u => (u, j u))), p.1 ≠ 0 := by
      rw [ae_iff]
      simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using hmass
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with p hp
    exact hF p hp
  · simp only [Measure.map_of_not_aemeasurable hf, integral_zero_measure]
end
