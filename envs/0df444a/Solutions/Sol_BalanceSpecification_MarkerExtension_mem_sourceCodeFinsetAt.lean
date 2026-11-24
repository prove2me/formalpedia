-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.mem_sourceCodeFinsetAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:19.229939+00:00
-- url     : https://prove2.me/submissions/9fd0a433-e1a9-4a22-b8f1-5aa036436743

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {n : ℕ} {z : Word (Option A)} :
    z ∈ sourceCodeFinsetAt M hM x s n ↔
      ∃ u : PositiveLanguage Y, u.val.length = n ∧
        none :: (sourcePayload M hM x s u).map some = z := by
  classical
  constructor
  · intro hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨⟨u.val, (mem_wordFinset.mp (Finset.mem_filter.mp u.property).1).1,
      (Finset.mem_filter.mp u.property).2⟩, ?_, rfl⟩
    exact (mem_wordFinset.mp (Finset.mem_filter.mp u.property).1).2
  · rintro ⟨u, hulen, rfl⟩
    apply Finset.mem_image.mpr
    let z : ↥((wordFinset (language Y) n).filter (fun v => 0 < v.length)) :=
      ⟨u.val, Finset.mem_filter.mpr ⟨mem_wordFinset.mpr ⟨u.property.1, hulen⟩,
        u.property.2⟩⟩
    exact ⟨z, Finset.mem_attach _ _, rfl⟩
end BalanceSpecification.MarkerExtension
