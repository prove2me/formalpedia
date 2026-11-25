-- Prove2me | solution 1 for Erdos919.exists_unbounded_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:37:18.322042+00:00
-- url     : https://prove2.me/submissions/74fe44d5-c301-4839-b1b0-0b20d5beea96

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_exists_gt_of_small

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution {α : Type u} (hα : #α ≤ ℵ₁) (d : W.{u} → α) :
    ∃ a, ∀ x, ∃ y, x ≤ y ∧ d y = a := by
  by_contra h
  push Not at h
  choose x hx using h
  obtain ⟨u, hu⟩ := exists_gt_of_small x hα
  exact hx (d u) u (hu (d u)).le rfl
end Erdos919
