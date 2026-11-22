-- Prove2me | solution 1 for DeciSigma1.Examples.unary_comparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:04.664688+00:00
-- url     : https://prove2.me/submissions/7519c008-92f6-4a7f-8b66-9287589e2204

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Theorems.Thm_DeciSigma1_Examples_unary_le_total

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints
namespace DeciSigma1.Examples
theorem _root_.solution :
    Entailment.DisjEntailsIn (fun _ => True) ([] : List (TopFree.Lit 1 (Fin 2))) swapQueries := by
  intro ρ _ _
  rcases unary_le_total (ρ 0) (ρ 1) with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
end DeciSigma1.Examples
