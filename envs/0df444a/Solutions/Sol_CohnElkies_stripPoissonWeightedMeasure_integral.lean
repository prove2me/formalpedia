-- Prove2me | solution 1 for CohnElkies.stripPoissonWeightedMeasure_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/952adb3b-e70d-4059-9010-2bb9245f9e45

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos

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
    (f : ℝ → ℝ) (s : ℝ) :
    (∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ s) =
      ∫ x : ℝ, stripPoissonKernel σ (s - x) * f x := by
  have hkreal : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hk : Measurable
      (fun x : ℝ =>
        ENNReal.ofReal (stripPoissonKernel σ (s - x))) :=
    hkreal.ennreal_ofReal
  have hfinite :
      ∀ᵐ x : ℝ ∂volume,
        ENNReal.ofReal (stripPoissonKernel σ (s - x)) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  unfold stripPoissonWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hk hfinite]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal
    (stripPoissonKernel_pos hbelow habove (s - x)).le]
  rfl
end CohnElkies
