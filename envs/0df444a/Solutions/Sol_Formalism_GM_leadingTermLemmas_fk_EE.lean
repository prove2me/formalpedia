-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_EE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:25.575797+00:00
-- url     : https://prove2.me/submissions/aa49db3a-3491-4501-92e5-a7afd616865d

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_symm
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_smul_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_E_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_harm_Epow
import Theorems.Thm_Formalism_GM_F_pow_E_pow
import Theorems.Thm_Formalism_GM_euler_e_of_biHom
import Theorems.Thm_Formalism_GM_euler_w_of_biHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hr : 1 ≤ r) {a b a' b' : ℕ} {u u' : MvPolynomial σ K} (hu : BiHom w e a b u)
    (hF : tieF w e u = 0) (hu' : BiHom w e a' b' u') (hF' : tieF w e u' = 0) (i j : ℕ) :
    fk ((tieE w e ^ i) u) ((tieE w e ^ j) u') =
      if i = j then ((j.descFactorial j * (a' + b' + r - 1 + j).descFactorial j : ℕ) : K) * fk u u'
      else 0 := by
  have hN' : a' + b' + r = (a' + b' + r - 1) + 1 := by omega
  have hN : a + b + r = (a + b + r - 1) + 1 := by omega
  have P' := F_pow_E_pow hw he hwe u' a' b' _ (euler_w_of_biHom w e hu') (euler_e_of_biHom w e hu') hF' hN'
  have P := F_pow_E_pow hw he hwe u a b _ (euler_w_of_biHom w e hu) (euler_e_of_biHom w e hu) hF hN
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg (by omega), fk_E_pow, P', fk_smul_right, fk_harm_Epow hw he hwe hF (by omega), mul_zero]
  · rw [if_pos rfl, fk_E_pow, P', fk_smul_right, Nat.sub_self, pow_zero, Module.End.one_apply]
  · rw [if_neg (by omega), fk_symm, fk_E_pow, P, fk_smul_right, fk_harm_Epow hw he hwe hF' (by omega),
      mul_zero]
end Formalism.GM.leadingTermLemmas
