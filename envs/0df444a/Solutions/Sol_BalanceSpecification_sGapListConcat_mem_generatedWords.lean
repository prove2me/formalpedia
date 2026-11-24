-- Prove2me | solution 1 for BalanceSpecification.sGapListConcat_mem_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:30.424159+00:00
-- url     : https://prove2.me/submissions/d1f3ca5d-208a-424d-a085-7346e38a8ad8

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {ss : List ℕ}
    (hs : ∀ s ∈ ss, s ∈ S) : sGapListConcat ss ∈ generatedWords (sGapCode S) := by
  refine ⟨ss.map (fun s => true :: List.replicate s false), ?_, rfl⟩
  intro w hw
  obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hw
  exact ⟨s, hs s hs', rfl⟩
end BalanceSpecification
