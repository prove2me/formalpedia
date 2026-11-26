-- Prove2me | solution 1 for FD1D.cdfTransportArea_sq_le_haarL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:33:31.887811+00:00
-- url     : https://prove2.me/submissions/41929d3a-d051-4cf6-bad1-71e1121379e4

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_haarCombination_integrable
import Theorems.Thm_FD1D_haarCombination_sq_integrable
import Theorems.Thm_FD1D_integral_abs_sq_le_integral_sq

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
theorem _root_.solution (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    cdfTransportArea (haarCombination l p b) ^ 2 ≤ haarL2 l p b := by
  have hsq := haarCombination_sq_integrable l p b hp
  calc
    cdfTransportArea (haarCombination l p b) ^ 2
        ≤ ∫ z in Icc (0 : ℝ) 1, haarCombination l p b z ^ 2 :=
      integral_abs_sq_le_integral_sq
        (haarCombination_integrable l p b).integrableOn hsq.integrableOn
    _ ≤ ∫ z, haarCombination l p b z ^ 2 := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun z => sq_nonneg (haarCombination l p b z)) hsq
    _ = haarL2 l p b := rfl
end FD1D
