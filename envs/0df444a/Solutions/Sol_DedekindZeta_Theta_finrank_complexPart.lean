-- Prove2me | solution 1 for DedekindZeta.Theta.finrank_complexPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:16:19.36919+00:00
-- url     : https://prove2.me/submissions/37924236-bbce-4439-b230-3068c8fe5750

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open Module
namespace DedekindZeta.Theta
theorem _root_.solution :
    finrank ℝ ({w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ)
      = 2 * nrComplexPlaces K := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [nrComplexPlaces, mul_comm]
end DedekindZeta.Theta
