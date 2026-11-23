-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.iso_mul_DG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:57.324926+00:00
-- url     : https://prove2.me/submissions/db03656a-6f21-4acb-8c40-8cba046847de

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_lamLin_mk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : ∀ j b : Fin n, j.val + 1 = n → ((((d j)⁻¹ : Kˣ) : K) - 1) * Z⁻¹ j b ∈ R) :
    Submodule.quotEquivOfEq _ _ (latZ_mul_DG R d hd Z) ∈
      isoZZ R Z (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  refine ⟨rfl, fun v v' hv => ?_⟩
  rw [Submodule.quotEquivOfEq_mk] at hv
  rw [← A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_apply, Formalism.DoubleCosetMeasures.P.lamLin_apply,
    Submodule.mkQ_apply, Submodule.mkQ_apply, A5x3.mk_eq_mk, Matrix.mul_inv_rev,
    ← Matrix.coe_units_inv, DG_inv_coe, ← Matrix.mulVec_mulVec, Formalism.DoubleCosetMeasures.P.lastCoord_apply,
    Formalism.DoubleCosetMeasures.P.lastCoord_apply, ← Finset.sum_sub_distrib]
  refine R.sum_mem fun j _ => ?_
  split_ifs with hj
  · rw [mulVec_diagonal, ← sub_one_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine R.sum_mem fun b _ => ?_
    rw [← mul_assoc, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    exact R.mul_mem (hA j b hj) (v b).2
  · simp
end Formalism.FourierDecayAlt.P.KernelScalingBack
