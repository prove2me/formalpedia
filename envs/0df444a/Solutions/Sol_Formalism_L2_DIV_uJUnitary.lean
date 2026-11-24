-- Prove2me | solution 1 for Formalism.L2.DIV.uJUnitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:41:28.235875+00:00
-- url     : https://prove2.me/submissions/4d273fc2-76dc-4543-9fed-1d2d99e6c551

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_embGL_coe
import Theorems.Thm_Formalism_L2_DIV_invTrK_coe
import Theorems.Thm_Formalism_L2_DIV_map_conjTranspose_eq
import Theorems.Thm_P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : UJUnitary := by
  intro E K _ _ _ ι n emb cE τ h J γ hγ
  have hγ' : Formalism.UG.cT cE (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have h1 : ((γ : Matrix (Fin n) (Fin n) E).map (emb τ))ᴴ * J.map (emb τ) * (γ : Matrix (Fin n) (Fin n) E).map (emb τ)
      = J.map (emb τ) := by
    rw [map_conjTranspose_eq (emb τ) cE h, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
  refine ⟨h1, fun _ => ?_⟩
  rw [invTrK_coe, Matrix.coe_units_inv, embGL_coe]
  unfold gramKd
  set g := (γ : Matrix (Fin n) (Fin n) E).map (emb τ) with hg
  set G := J.map (emb τ) with hG
  rw [conjTranspose_transpose', ← Matrix.transpose_mul, ← Matrix.transpose_mul, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, h1]
end Formalism.L2.DIV
