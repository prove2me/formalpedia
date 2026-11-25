-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.mulOp_comm_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:42.286696+00:00
-- url     : https://prove2.me/submissions/cf44fa1c-9834-4d90-ad2b-dc221ba53ff0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_opL_fsv_smul_other
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_radSp_regular
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_add_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_alg_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_mul_snd
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_fst
attribute [local simp] Formalism.FourierDecayAlt.P5.pr_one_snd
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
attribute [local simp] P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e



set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π')) (t : ℂ) (l : Fin r)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    {l' : Fin r} (hl : l' ≠ l) (i : Fin 6) : W * X.op l' i = X.op l' i * W := by
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  have hop : ∀ (Ψ : RadSp k r z z' π π'),
      (X.op l' i Ψ : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l' i) (Ψ : Fn k r (Wq →L[ℂ] Wp)) :=
    fun Ψ => X.op_apply l' i Ψ
  simp only [Module.End.mul_apply, hW, hop, crd]
  exact (opL_fsv_smul_other t hl i _ c (radSp_regular Φ g c).1).symm
end Formalism.FourierDecayAlt.P5
