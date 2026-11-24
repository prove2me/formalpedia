-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution.partial_coboundary_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:22.600143+00:00
-- url     : https://prove2.me/submissions/dcd6b121-48b1-4b33-a772-167da29f3cab

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_PartialCoboundaryLinear
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0) (k q : K)
    (P G : MvPowerSeries (Fin 2) K) :
    d1 F (MvPowerSeries.C k * (P - MvPowerSeries.C q * G)) =
      MvPowerSeries.C k * (d1 F P - MvPowerSeries.C q * d1 F G) := by
  have h1 : MvPowerSeries.HasSubst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    MvPowerSeries.HasSubst.cons_subst_zero_left 0 1 2 hF0
  have h2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    MvPowerSeries.HasSubst.X_X
  have h3 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    MvPowerSeries.HasSubst.X_X
  have hc : ∀ (ψ : MvPowerSeries (Fin 2) K →ₐ[K] MvPowerSeries (Fin 3) K) (a : K),
      ψ (MvPowerSeries.C a) = MvPowerSeries.C a := fun ψ a => by
    first
      | exact ψ.commutes a
      | (have h := ψ.commutes a; rwa [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h)
      | simp
  unfold d1
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2,
    ← MvPowerSeries.coe_substAlgHom h3]
  simp only [map_mul, map_sub, hc]
  ring
end Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
