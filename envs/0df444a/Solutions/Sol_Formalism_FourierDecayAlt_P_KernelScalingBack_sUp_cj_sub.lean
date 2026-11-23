-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_cj_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:46.305798+00:00
-- url     : https://prove2.me/submissions/f9cda86e-71ed-4f86-b786-e5793cf6caf3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
theorem _root_.solution (d : Fin n → Kˣ) (y : GL (Fin n) K)
    (hB : ∀ (j : Fin n) (hj : j.val + 1 < n),
      ((((d j)⁻¹ : Kˣ) : K) * ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ ∈ R) :
    sUp ((cj d y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      sUp (y : Matrix (Fin n) (Fin n) K) ∈ R := by
  unfold sUp
  rw [← Finset.sum_sub_distrib]
  refine R.sum_mem fun j _ => ?_
  split_ifs with hj
  · rw [cj_apply]
    have := hB j hj
    have e : (((d j)⁻¹ : Kˣ) : K) * (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ *
        ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ =
        ((((d j)⁻¹ : Kˣ) : K) * ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ := by ring
    rw [e]; exact this
  · simp
end Formalism.FourierDecayAlt.P.KernelScalingBack
