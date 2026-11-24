-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.rc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:03.735335+00:00
-- url     : https://prove2.me/submissions/9427848c-6dbd-4f72-a1d1-7f5eba049a51

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_toV
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sandw_hat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_vAB_hat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_vABs_hat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : HatData (Fn k r E))
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) (j : ℕ) (M : OM (Fn k r E))
    (hM : ∀ a b, H.Good (M a b)) {Φ : Fn k r E} (hΦ : Φ ∈ H.G) :
    H.N (sandw k r Y j M 0 0 Φ) =
      H.N (∑ a : Fin 2, ∑ b : Fin 2, crd (cmp (vABs r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) := by
  obtain ⟨g1, h1⟩ := sandw_hat hop Y j M hM
  have gv := fun b => (vAB_hat (H := H) hop Y j b).1
  have hv := fun b => (vAB_hat (H := H) hop Y j b).2
  have gs := fun a => (vABs_hat (H := H) hop Y j a).1
  have hs := fun a => (vABs_hat (H := H) hop Y j a).2
  have gt : ∀ a b, H.Good (fun Φ => crd (cmp (vABs (E := E) r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) :=
    fun a b => (gs a).comp ((hM a b).comp (gv b))
  have ht : ∀ a b, H.hat (fun Φ => crd (cmp (vABs (E := E) r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) =
      Lp H Y j 0 a * (hatM H M a b * Rp H Y j b 0) := by
    intro a b
    rw [HatData.hat_comp (gs a) ((hM a b).comp (gv b)), HatData.hat_comp (hM a b) (gv b), hs, hv]
    rfl
  have gW := ((gt 0 0).add (gt 0 1)).add ((gt 1 0).add (gt 1 1))
  have hW : H.hat (sandw k r Y j M 0 0) = H.hat (fun Φ =>
      (crd (cmp (vABs (E := E) r Y j) 0) (M 0 0 (crd (cmp (vAB r Y j) 0) Φ)) +
        crd (cmp (vABs (E := E) r Y j) 0) (M 0 1 (crd (cmp (vAB r Y j) 1) Φ))) +
      (crd (cmp (vABs (E := E) r Y j) 1) (M 1 0 (crd (cmp (vAB r Y j) 0) Φ)) +
        crd (cmp (vABs (E := E) r Y j) 1) (M 1 1 (crd (cmp (vAB r Y j) 1) Φ)))) := by
    rw [HatData.hat_add ((gt 0 0).add (gt 0 1)) ((gt 1 0).add (gt 1 1)), HatData.hat_add (gt 0 0) (gt 0 1),
      HatData.hat_add (gt 1 0) (gt 1 1), ht, ht, ht, ht]
    have := congrFun (congrFun h1 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two] at this
    refine this.trans ?_
    noncomm_ring
  have h2 := congrArg (fun T => ((T (H.toV Φ hΦ) : H.V) : Fn k r E)) hW
  simp only [HatData.hat_toV (g1 0 0) hΦ, HatData.hat_toV gW hΦ] at h2
  simp only [Fin.sum_univ_two]
  exact h2
end Formalism.FourierDecayAlt.P.Qx6
