-- Prove2me | solution 1 for CohnElkies.even_antitone_poisson_lintegral_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/69fcda74-edbd-4d90-baac-c77c969cb2c9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_superlevel_le

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
    {f : ℝ → ℝ} {B : ℝ}
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫⁻ x : ℝ,
      ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ s) ≤
      ∫⁻ x : ℝ,
        ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ 0 := by
  rw [lintegral_eq_lintegral_meas_lt
    (stripPoissonWeightedMeasure σ s)
      (Filter.Eventually.of_forall hfnonneg)
      hfmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt
      (stripPoissonWeightedMeasure σ 0)
      (Filter.Eventually.of_forall hfnonneg)
      hfmeas.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with t ht
  exact stripPoissonWeightedMeasure_superlevel_le
    hbelow habove heven hanti hsupport ht s
end CohnElkies
