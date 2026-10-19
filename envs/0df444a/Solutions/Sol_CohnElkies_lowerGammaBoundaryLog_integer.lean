-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/84631932-385d-4a55-b82d-357d07338a7e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integer_gamma_product
import Theorems.Thm_CohnElkies_norm_integerGammaFactor
import Theorems.Thm_CohnElkies_integerGammaFactor_ne_zero
import Theorems.Thm_CohnElkies_gamma_imaginary_ne_zero
import Theorems.Thm_CohnElkies_norm_gamma_neg_imaginary

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R y =
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
  have hbase :
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_imaginary_ne_zero hy)
  have hproduct :
      (∏ j ∈ Finset.range k,
        ((j : ℂ) + Complex.I * (y : ℂ) / 2)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun j _ => integerGammaFactor_ne_zero j hy)
  have hproductnorm :
      ‖∏ j ∈ Finset.range k,
        ((j : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hproduct
  have hlogproduct :
      Real.log
        ‖∏ j ∈ Finset.range k,
          ((j : ℂ) + Complex.I * (y : ℂ) / 2)‖ =
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod]
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j _
      rw [norm_integerGammaFactor]
    · intro j _
      exact norm_ne_zero_iff.mpr (integerGammaFactor_ne_zero j hy)
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by
    norm_cast
  unfold lowerGammaBoundaryLog
  rw [hcast, integer_gamma_product k hy, norm_mul,
    Real.log_mul hbase hproductnorm, norm_gamma_neg_imaginary,
    hlogproduct]
  ring
end CohnElkies
