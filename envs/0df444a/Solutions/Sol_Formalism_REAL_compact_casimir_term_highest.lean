-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_term_highest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:03.736079+00:00
-- url     : https://prove2.me/submissions/1ad9a634-f96b-44f7-9d50-63ed4d8647cc

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_lie_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) {a b : Fin n}
    (hab : ε a = ε b) :
    F a b (F b a x) = ((if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0 : ℝ) : ℂ) • x := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have := compact_lie_commutator h hab hab.symm x
    rw [hx.2 a b hlt hab, map_zero, sub_zero, if_pos rfl, if_pos rfl, hx.1 a, hx.1 b] at this
    rw [this, if_neg hlt.ne, if_pos hlt]
    push_cast
    rw [sub_smul]
  · rw [hx.1 a, map_smul, hx.1 a, smul_smul, if_pos rfl]
    push_cast
    rw [sq]
  · rw [hx.2 b a hgt hab.symm, map_zero, if_neg hgt.ne', if_neg (not_lt.mpr hgt.le)]
    simp
end Formalism.REAL
