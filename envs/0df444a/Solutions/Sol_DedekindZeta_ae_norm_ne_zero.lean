-- Prove2me | solution 1 for DedekindZeta.ae_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:19.001641+00:00
-- url     : https://prove2.me/submissions/6cd74690-6832-42a8-9b06-e8753bb9caff

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction
attribute [local instance] DedekindZeta.coneMeasurableConstSMul
attribute [local instance] DedekindZeta.coneCountable
attribute [local instance] DedekindZeta.coneSMulInvariantMeasure
variable {K}
namespace DedekindZeta
theorem _root_.solution :
    ∀ᵐ x ∂(mixedMulHaar K), mixedEmbedding.norm x ≠ 0 := by
  rw [ae_iff]
  have hset : {x : mixedEmbedding.mixedSpace K | ¬ mixedEmbedding.norm x ≠ 0}
      = {x | mixedEmbedding.norm x = 0} := by
    ext x; simp
  rw [hset]
  have hms : MeasurableSet {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x = 0} :=
    measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const
  rw [mixedMulHaar, withDensity_apply _ hms]
  refine setLIntegral_eq_zero hms ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp [hx]
end DedekindZeta
