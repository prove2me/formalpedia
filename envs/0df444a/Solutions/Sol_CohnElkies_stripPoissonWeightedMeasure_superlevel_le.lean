-- Prove2me | solution 1 for CohnElkies.stripPoissonWeightedMeasure_superlevel_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/2ec991ea-c2c4-4ccf-86f8-ceb4149dfea1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_even_antitone_superlevel_interval
import Theorems.Thm_CohnElkies_stripPoissonWeightedMeasure_centered_interval_max

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
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) (s : ℝ) :
    stripPoissonWeightedMeasure σ s
        {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ 0
        {x : ℝ | t < f x} := by
  obtain ⟨r, hr, hinner, houter⟩ :=
    even_antitone_superlevel_interval heven hanti hsupport ht
  have hinterval :
      stripPoissonWeightedMeasure σ 0 (Ioo (-r) r) =
        stripPoissonWeightedMeasure σ 0 (Icc (-r) r) := by
    unfold stripPoissonWeightedMeasure
    exact measure_congr Ioo_ae_eq_Icc
  calc
    stripPoissonWeightedMeasure σ s
        {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ s
        (Icc (-r) r) :=
      measure_mono houter
    _ ≤ stripPoissonWeightedMeasure σ 0
        (Icc (-r) r) :=
      stripPoissonWeightedMeasure_centered_interval_max
        hbelow habove hr s
    _ = stripPoissonWeightedMeasure σ 0
        (Ioo (-r) r) :=
      hinterval.symm
    _ ≤ stripPoissonWeightedMeasure σ 0
        {x : ℝ | t < f x} :=
      measure_mono hinner
end CohnElkies
