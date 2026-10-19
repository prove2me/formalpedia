-- Prove2me | solution 1 for CohnElkies.stripPoissonWeightedMeasure_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/5b01530b-6c86-498c-8967-244360cb5f50

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_weighted_product_integrable

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
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable f (stripPoissonWeightedMeasure σ s) := by
  have hkreal : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hknn : Measurable
      (fun x : ℝ =>
        Real.toNNReal (stripPoissonKernel σ (s - x))) :=
    hkreal.real_toNNReal
  unfold stripPoissonWeightedMeasure
  change Integrable f
    ((volume : Measure ℝ).withDensity
      (fun x : ℝ =>
        (Real.toNNReal (stripPoissonKernel σ (s - x)) : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_smul hknn).2
  have hproduct :=
    stripPoissonKernel_weighted_product_integrable
      hbelow habove hf s
  convert! hproduct using 1
  ext x
  simp [NNReal.smul_def,
    Real.coe_toNNReal _
      (stripPoissonKernel_pos hbelow habove (s - x)).le,
    smul_eq_mul]
end CohnElkies
