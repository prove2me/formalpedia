-- Prove2me | solution 1 for DeciSigma1.Examples.unary_le_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:25.196581+00:00
-- url     : https://prove2.me/submissions/e63c54f8-4e9b-424a-9067-09ebbfd911ab

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
public import Theorems.Thm_DeciSigma1_Examples_unary_mem_of_length_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints
namespace DeciSigma1.Examples
theorem _root_.solution (t u : PrefixSet 1) : t ≤ u ∨ u ≤ t := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  have h₁' : ¬ t.carrier ⊆ u.carrier := h₁
  have h₂' : ¬ u.carrier ⊆ t.carrier := h₂
  obtain ⟨w, hwt, hwu⟩ := Set.not_subset.mp h₁'
  obtain ⟨v, hvu, hvt⟩ := Set.not_subset.mp h₂'
  rcases le_total w.length v.length with hl | hl
  · exact hwu (unary_mem_of_length_le u hl hvu)
  · exact hvt (unary_mem_of_length_le t hl hwt)
end DeciSigma1.Examples
