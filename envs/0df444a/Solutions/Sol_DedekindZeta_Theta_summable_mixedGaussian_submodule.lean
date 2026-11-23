-- Prove2me | solution 1 for DedekindZeta.Theta.summable_mixedGaussian_submodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:25.99789+00:00
-- url     : https://prove2.me/submissions/c61691b6-9472-4af2-a2a9-e019f894f3c8

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_discreteTopology_idealLattice
import Theorems.Thm_DedekindZeta_Theta_isZLattice_idealLattice
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_PoissonSummation_summable_periodisation

attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    Summable (fun a : (J : Submodule (𝓞 K) K) =>
      (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)) := by
  haveI := discreteTopology_idealLattice K J hJ
  haveI := isZLattice_idealLattice K J hJ
  have hL : Summable (fun v : idealLattice K J =>
      (mixedGaussianSchwartz K hy : minkowskiSpace K → ℂ) v) := by
    have h := PoissonSummation.summable_periodisation (idealLattice K J)
      (mixedGaussianSchwartz K hy) 0
    simpa using h
  have h2 := (Equiv.summable_iff (idealLatticeEquiv K J)).mpr hL
  refine h2.congr (fun a => ?_)
  simp only [Function.comp_apply]
  rw [mixedGaussianSchwartz_apply]
  have hv : ((idealLatticeEquiv K J a : idealLattice K J) : minkowskiSpace K)
      = toMinkowski K (mixedEmbedding K (a : K)) := rfl
  rw [hv, ContinuousLinearEquiv.symm_apply_apply]
end DedekindZeta.Theta
