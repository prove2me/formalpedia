-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.comm_xt_of_fsv_smul_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:44:37.447657+00:00
-- url     : https://prove2.me/submissions/f22d9291-17b6-4079-b9c8-eb45f147dd3b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_tL_smulC
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_add_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_alg_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_mul_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P5_pr_one_snd
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
    (Y : ℂ) (a b : Fin 2) : W * X.t Y a b = X.t Y a b * W := by
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  simp only [Module.End.mul_apply]
  rw [hW]
  by_cases hx : (c, g) ∈ DomR k r z z'
  · have h1 := X.t_apply Y a b Φ (c, g) hx
    have h2 := X.t_apply Y a b (W Φ) (c, g) hx
    simp only at h1 h2
    have hWc : (W Φ : Fn k r (Wq →L[ℂ] Wp)) c = fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c := by
      funext g'; rw [hW]; rfl
    rw [h1, h2, hWc, tL_smulC z z' _ Y a b]
    rfl
  · rw [(X.t Y a b Φ).2.1 (c, g) hx, (X.t Y a b (W Φ)).2.1 (c, g) hx, smul_zero]
end Formalism.FourierDecayAlt.P5
