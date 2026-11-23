-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.mem_isoZZ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.982751+00:00
-- url     : https://prove2.me/submissions/5c3e4782-614d-493d-a2c8-d96725a05338

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_muZ_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_lamLin_out
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det) (θ : coker R Z ≃ₗ[R] coker R Z') :
    θ ∈ isoZZ R Z Z' ↔ eZ R Z - θ.symm (eZ R Z') = 0 ∧
      muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0 := by
  rw [sub_eq_zero, sub_eq_zero, LinearEquiv.eq_symm_apply]
  simp only [isoZZ, Set.mem_setOf_eq]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h v v' hv => ?_⟩
  · refine LinearMap.ext fun β => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ β
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, muZ_mk]
    rw [← lamLin_out R Z' hZ']
    exact (h v _ (Quotient.out_eq _).symm).symm
  · rw [← muZ_mk R Z' hZ' v', ← hv, ← muZ_mk R Z hZ v, h]
    rfl
end Formalism.FourierDecayAlt.P.A5x6
