-- Prove2me | solution 1 for CohnElkies.stripPoissonWeightedMeasure_apply_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/6583d9d9-41cc-463f-b051-23b80f18ab11

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s a b : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc a b) =
      ENNReal.ofReal
        (∫ x in Icc a b,
          stripPoissonKernel σ (s - x)) := by
  unfold stripPoissonWeightedMeasure
  rw [MeasureTheory.withDensity_apply _ measurableSet_Icc]
  have hint :
      IntegrableOn
        (fun x : ℝ => stripPoissonKernel σ (s - x))
        (Icc a b) :=
    ((stripPoissonKernel_integrable hbelow habove).comp_sub_left s).integrableOn
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc a b)]
        (fun x : ℝ => stripPoissonKernel σ (s - x)) :=
    Filter.Eventually.of_forall
      (fun x => (stripPoissonKernel_pos hbelow habove (s - x)).le)
  exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
end CohnElkies
