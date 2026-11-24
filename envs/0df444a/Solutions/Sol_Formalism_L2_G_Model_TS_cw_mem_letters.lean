-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_mem_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:48.058581+00:00
-- url     : https://prove2.me/submissions/6ed7e112-6d8d-42ae-849c-573c7c77063b

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ cwLetters r n ↔ l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val := by
  obtain ⟨s, a, a', s'⟩ := l
  simp only [cwLetters, List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨t, b, hb⟩
    split_ifs at hb with h
    · simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
      exact ⟨rfl, rfl, h.1⟩
  · rintro ⟨e1, e2, e3⟩
    have e1' : a' = a := e1
    have e2' : s'.val = s.val := e2
    have e3' : s.val < a.val := e3
    subst e1'
    refine ⟨s', a', ?_⟩
    rw [dif_pos ⟨by omega, by omega⟩]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact Fin.ext e2'
end Formalism.L2.G.Model.TS
