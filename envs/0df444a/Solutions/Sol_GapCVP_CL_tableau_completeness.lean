-- Prove2me | solution 1 for GapCVP.CL.tableau_completeness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/43f260ed-c7ed-42d9-907d-8458eef17bef

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_atLeastOneClause_satisfied
import Theorems.Thm_GapCVP_CL_atMostOneClause_satisfied
import Theorems.Thm_GapCVP_CL_initialClause_satisfied
import Theorems.Thm_GapCVP_CL_acceptanceClause_satisfied
import Theorems.Thm_GapCVP_CL_transitionClause_satisfied

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
    (trace : Time T → Position T → Symbol S)
    (htrace : ValidTrace spec trace) :
    satisfiesFormula (assignmentOfTrace trace) (tableauFormula spec) := by
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq]
  have htrace' := htrace
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq] at htrace'
  intro clause hclause
  simp only [tableauFormula, Finset.mem_union, Finset.mem_singleton] at hclause
  rcases hclause with ((hstruct | hinit) | haccept) | htransition
  · simp only [structuralClauses, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hstruct
    rcases hstruct with ⟨p, rfl⟩ | ⟨p, hp, rfl⟩
    · exact atLeastOneClause_satisfied trace p.1 p.2
    · exact atMostOneClause_satisfied trace p.1.1 p.1.2
        p.2.1 p.2.2 hp
  · simp only [initialClauses, Finset.mem_image,
      Finset.mem_univ, true_and] at hinit
    obtain ⟨i, rfl⟩ := hinit
    exact initialClause_satisfied spec trace htrace'.1 i
  · subst clause
    exact acceptanceClause_satisfied spec trace htrace'.2.1
  · simp only [transitionClauses, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at htransition
    obtain ⟨p, hp, rfl⟩ := htransition
    exact transitionClause_satisfied spec trace htrace'.2.2 p.1 p.2 hp
end GapCVP.CL
