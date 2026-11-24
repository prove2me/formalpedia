-- Prove2me | solution 1 for Formalism.UG.P.satake_subset_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:53:05.696061+00:00
-- url     : https://prove2.me/submissions/6fc93063-dfd0-4766-9618-44ae499f7260

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satakeN_mul_diag
import Theorems.Thm_Formalism_UG_P_satakeN_diag
import Theorems.Thm_Formalism_UG_P_satake_glint_entry
import Theorems.Thm_Formalism_UG_P_satakeGL_inv_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
private lemma one_sub_satakeN_mul_one_add_satakeN_diag (S S' : Finset (Fin n)) (c : satakePairs S → O)
    (c' : satakePairs S' → O) (a : Fin n) :
    ((1 - satakeN O S c) * (1 + satakeN O S' c')) a a = 1 := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
    Matrix.add_apply, Matrix.one_apply_eq, satakeN_diag, satakeN_mul_diag, add_zero, sub_zero]
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution {π : L} (hπ : π ≠ 0) (hπO : π⁻¹ ∉ O) (S S' : Finset (Fin n))
    (c : satakePairs S → O) (c' : satakePairs S' → O)
    (h : (satakeGL O hπ S c)⁻¹ * satakeGL O hπ S' c' ∈ GLint (Fin n) O) : S ⊆ S' := by
  intro a ha
  by_contra ha'
  have h1 := satake_glint_entry O h a a
  rw [satakeGL_inv_mul_apply, one_sub_satakeN_mul_one_add_satakeN_diag, if_pos ha, if_neg ha', mul_one, mul_one] at h1
  exact hπO h1
end Formalism.UG.P
