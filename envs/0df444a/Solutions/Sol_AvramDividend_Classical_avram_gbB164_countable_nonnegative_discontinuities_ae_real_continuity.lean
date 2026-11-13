-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:11:11.1098+00:00
-- url     : https://prove2.me/submissions/397ff953-2407-478d-b0c8-558d24dc5de5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ)
    (hc : Set.Countable {u : ℝ≥0 | ¬ ContinuousAt f u})
    (n : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun r : ℝ => f (Real.toNNReal r)) t := by
  let S : Set ℝ := (fun u : ℝ≥0 => (u : ℝ)) ''
    {u : ℝ≥0 | ¬ ContinuousAt f u}
  have hcS : S.Countable :=
    hc.image (fun u : ℝ≥0 => (u : ℝ))
  have hzero : volume S = 0 := hcS.measure_zero volume
  have hAE : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ S := by
    apply (ae_iff).2
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  have hR : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      t ∉ S := ae_restrict_of_ae hAE
  filter_upwards [hR, ae_restrict_mem measurableSet_Ioo] with t htS ht
  by_contra hNot
  have hDisc : ¬ ContinuousAt f (Real.toNNReal t) := by
    intro hCont
    apply hNot
    simpa only [Function.comp_def] using
      (hCont.comp continuous_real_toNNReal.continuousAt)
  have hEq : ((Real.toNNReal t : ℝ≥0) : ℝ) = t :=
    Real.coe_toNNReal t (le_of_lt ht.1)
  exact htS ⟨Real.toNNReal t, hDisc, hEq⟩
