-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.closure_normEqOneSurface_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:45.979618+00:00
-- url     : https://prove2.me/submissions/17215a7d-9d42-47fc-8301-148cc2d84560

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution :
    closure (normEqOneSurface K) ⊆ {x : mixedSpace K | mixedEmbedding.norm x = 1} := by
  have hclosed : IsClosed {x : mixedSpace K | mixedEmbedding.norm x = 1} :=
    isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const
  refine closure_minimal (fun x hx => ?_) hclosed
  exact (mem_normEqOneSurface.mp hx).2
end DedekindZeta.ConeRadialReduction
