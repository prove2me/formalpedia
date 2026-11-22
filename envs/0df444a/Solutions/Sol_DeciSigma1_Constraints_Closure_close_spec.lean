-- Prove2me | solution 1 for DeciSigma1.Constraints.Closure.close_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:31.105794+00:00
-- url     : https://prove2.me/submissions/45eb26a6-da49-4350-ac9b-cf868411fb0e

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Closure_expand_sound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
open DeciSigma1.Constraints.Closure
namespace DeciSigma1.Constraints.Closure
theorem _root_.solution (Γ : List (LitT n V)) (s : Finset (V × V)) :
    s ⊆ close Γ s ∧ expand Γ (close Γ s) ⊆ close Γ s ∧
    ((∀ p ∈ s, Derives Γ p.1 p.2) → ∀ p ∈ close Γ s, Derives Γ p.1 p.2) := by
  fun_induction close Γ s with
  | case1 s hs => exact ⟨Finset.Subset.refl _, hs, fun h => h⟩
  | case2 s _ ih =>
    exact ⟨Finset.Subset.trans Finset.subset_union_left ih.1, ih.2.1,
      fun hs => ih.2.2 (expand_sound Γ s hs)⟩
end DeciSigma1.Constraints.Closure
