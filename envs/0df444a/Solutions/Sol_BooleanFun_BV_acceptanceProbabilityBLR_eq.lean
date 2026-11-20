-- Prove2me | solution 1 for BooleanFun.BV.acceptanceProbabilityBLR_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:53.223336+00:00
-- url     : https://prove2.me/submissions/7ee415dd-c915-41b8-a207-8abf47b299d6

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_BooleanFun_BV_oneOn_eq_of_one_or_neg_one

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) : acceptanceProbabilityBLR f =
    (𝐄 <| fun x ↦ 𝐄 <| fun y ↦ (1/2) * (1 + (f x) * (f y) * (f (x + y)))) := by
  have hl : ∀ x y, (f x) * (f y) = 1 ∨ (f x) * (f y) = -1 := by
    intro x y
    obtain ⟨hx|hx, hy|hy⟩ := And.intro (hbv.one_or_neg_one x) (hbv.one_or_neg_one y) <;>
      { rw [hx, hy]; simp }
  simp_rw [acceptanceProbabilityBLR, oneOn_eq_of_one_or_neg_one (hl _ _) (hbv.one_or_neg_one _)]
end BooleanFun.BV
