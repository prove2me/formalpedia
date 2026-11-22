-- Prove2me | solution 1 for DeciSigma1.Constraints.Closure.expand_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:45.305543+00:00
-- url     : https://prove2.me/submissions/d761532a-7d76-4406-9358-fc4d7e1c87be

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Closure_mem_expand

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
open DeciSigma1.Constraints.Closure
namespace DeciSigma1.Constraints.Closure
theorem _root_.solution (Γ : List (LitT n V)) (s : Finset (V × V))
    (hs : ∀ p ∈ s, Derives Γ p.1 p.2) :
    ∀ p ∈ expand Γ s, Derives Γ p.1 p.2 := by
  rintro ⟨x, y⟩ hp
  rcases (mem_expand Γ s x y).mp hp with
    hp | rfl | hl | ⟨z, hxz, hzy⟩ | ⟨a, u, v, b, i, hl, huv, hu, rfl, rfl⟩
  · exact hs _ hp
  · exact Derives.refl x
  · exact Derives.lit hl
  · exact Derives.trans (hs (x, z) hxz) (hs (z, y) hzy)
  · exact Derives.decomp i hl (hs _ huv) hu
end DeciSigma1.Constraints.Closure
