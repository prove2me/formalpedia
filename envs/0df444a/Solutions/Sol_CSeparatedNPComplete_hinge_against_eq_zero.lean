-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_against_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:06.676318+00:00
-- url     : https://prove2.me/submissions/4a697366-8cf5-477c-b504-7efb437df321

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n))
    (h : ∀ b ∈ L, gaussian_pair_hinge c a g b = 0) : hinge_against c a g L = 0 := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [hinge_against, h b (by simp), zero_add]
    exact ih fun x hx => h x (by simp [hx])
end CSeparatedNPComplete
