-- Prove2me | solution 1 for GapCVP.CL.symbol_unique_of_satisfiesFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/00b6ece6-9cfd-4b27-b433-2b8b8a961efd

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CL
namespace GapCVP.CL
theorem _root_.solution {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T)
    (a b : Symbol S)
    (ha : assignment (t, i, a) = true)
    (hb : assignment (t, i, b) = true) : a = b := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  have exclude (a b : Symbol S) (hab : a < b)
      (ha : assignment (t, i, a) = true)
      (hb : assignment (t, i, b) = true) : False := by
    obtain ⟨literal, hliteral, hvalue⟩ :=
      hsat' (atMostOneClause t i a b)
        (atMostOneClause_mem_tableauFormula spec t i a b hab)
    simp only [atMostOneClause, Finset.mem_insert,
      Finset.mem_singleton] at hliteral
    rcases hliteral with hleft | hright
    · subst literal
      have hfalse : assignment (t, i, a) = false := by
        simpa [negative] using hvalue
      simp [ha] at hfalse
    · subst literal
      have hfalse : assignment (t, i, b) = false := by
        simpa [negative] using hvalue
      simp [hb] at hfalse
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (exclude a b hab ha hb).elim
  · exact hab
  · exact (exclude b a hab hb ha).elim
end GapCVP.CL
