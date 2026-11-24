-- Prove2me | solution 1 for Formalism.UG.P.satake_entry_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:45.749014+00:00
-- url     : https://prove2.me/submissions/f9476cbe-cbf2-4c2b-9cff-7aba5884bd73

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satake_glint_entry
import Theorems.Thm_Formalism_UG_P_satakeGL_inv_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c c' : satakePairs S → O)
    (h : (satakeGL O hπ S c)⁻¹ * satakeGL O hπ S c' ∈ GLint (Fin n) O) (p : satakePairs S) :
    π⁻¹ * (((c' p : O) : L) - ((c p : O) : L)) ∈ O := by
  obtain ⟨⟨a, l⟩, ha, hl, hal⟩ := p
  have h1 := satake_glint_entry O h a l
  rw [satakeGL_inv_mul_apply, if_pos ha, if_neg hl, mul_one, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_add, satakeN_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, add_zero,
    Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply_ne hal.ne, satakeN_apply O S c' a l,
    satakeN_apply O S c a l, dif_pos ⟨ha, hl, hal⟩, dif_pos ⟨ha, hl, hal⟩, zero_add] at h1
  exact h1
end Formalism.UG.P
