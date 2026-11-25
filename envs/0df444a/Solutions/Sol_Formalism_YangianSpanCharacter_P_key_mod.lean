-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.key_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:23.228816+00:00
-- url     : https://prove2.me/submissions/1722b95c-1fa3-4739-bef1-456edc9560cd

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Theorems.Thm_Formalism_YangianSpanCharacter_P_from_comm
import Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4
import Theorems.Thm_Formalism_YangianSpanCharacter_P_key_alg
import Theorems.Thm_Formalism_YangianSpanCharacter_P_commutator_of_modular_relation
import Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc
import Theorems.Thm_Formalism_YangianSpanCharacter_P_mu_symm
import Theorems.Thm_Formalism_YangianSpanCharacter_P_diagonal_entry_eq_of_modular_relation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hu1 : u + 1 ∈ S) (hv : v ∈ S)
    (hv1 : v + 1 ∈ S) (huv : u ≠ v) :
    (u - v - 1) • (mf t τinv u * lf t τinv v - lf t τinv v * mf t τinv u) =
      hf τinv q v - hf τinv q u - (mf t τinv u * lf t τinv u - lf t τinv u * mf t τinv u) := by
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hau : t u 1 1 * mf t τinv u = t u 0 1 := by
    simp only [mf]; rw [← mul_assoc, (H.2.2.2.1 u hu).1, one_mul]
  have hbv : t v 1 1 * lf t τinv v = t v 1 0 := by
    simp only [lf]; rw [← mul_assoc, (H.2.2.2.1 v hv).1, one_mul]
  have hR : (u - v) • (t u 1 1 * mf t τinv u * (t v 1 1 * lf t τinv v) -
      t v 1 1 * lf t τinv v * (t u 1 1 * mf t τinv u)) =
      t u 1 1 * (t v 1 1 * (mf t τinv v * lf t τinv v + hf τinv q v)) -
        t v 1 1 * (t u 1 1 * (mf t τinv u * lf t τinv u + hf τinv q u)) := by
    rw [hau, hbv, ← diagonal_entry_eq_of_modular_relation H hv hv1, ← diagonal_entry_eq_of_modular_relation H hu hu1]
    exact H.1 u v 0 1 1 0
  have h1 := from_comm (commutator_of_modular_relation H hu hv huv)
  have h2 : mf t τinv u * t v 1 1 = t v 1 1 * (mf t τinv u - mu t τinv u v) := by
    have h := y1'_mod H hv hu (Ne.symm huv)
    rw [mu_symm] at h
    exact from_comm' h
  have hη : (u - v) • eta t τinv u v = lf t τinv u - lf t τinv v := by
    simp only [eta]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  have hμ : (u - v) • mu t τinv u v = mf t τinv u - mf t τinv v := by
    simp only [mu]; rw [smul_smul, mul_inv_cancel₀ huv', one_smul]
  exact key_alg (H.2.2.2.1 u hu).2 (H.2.2.2.1 v hv).2 (H.2.2.2.2.1 u v).eq h1 h2 hη hμ hR
end Formalism.YangianSpanCharacter.P
