-- Prove2me | solution 1 for DeciSigma1.Constraints.Closure.decompStep_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:11.587332+00:00
-- url     : https://prove2.me/submissions/effcdd86-706e-48f2-b1df-f1da6f44ed61

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
open DeciSigma1.Constraints.Closure
omit [Fintype V] [DecidableEq V]
namespace DeciSigma1.Constraints.Closure
theorem _root_.solution (Γ : List (LitT n V)) (s : Finset (V × V)) (x y : V) :
    DecompStep Γ s x y ↔
      ∃ a u v b i, LitT.fLe a u ∈ Γ ∧ (u, v) ∈ s ∧ LitT.leF v b ∈ Γ ∧
        a i = x ∧ b i = y := by
  constructor
  · rintro ⟨⟨a, u⟩, hl, ⟨v, b⟩, hm, hs, i, hx, hy⟩
    exact ⟨a, u, v, b, i, (mem_lowerLits Γ a u).mp hl, hs,
      (mem_upperLits Γ v b).mp hm, hx, hy⟩
  · rintro ⟨a, u, v, b, i, hl, hs, hu, hx, hy⟩
    exact ⟨(a, u), (mem_lowerLits Γ a u).mpr hl, (v, b), (mem_upperLits Γ v b).mpr hu,
      hs, i, hx, hy⟩
end DeciSigma1.Constraints.Closure
