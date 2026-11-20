-- Prove2me | solution 1 for BooleanFun.BV.oneOn_NAE3_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:57.549176+00:00
-- url     : https://prove2.me/submissions/cbbc134f-8040-4267-9f85-e6b09802c9fc

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow

set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) {x y z : Fin n → Fin 2}:
    oneOn (NAE3 (f x) (f y) (f z)) = 3/4 - (1/4) * (f x) * (f y) - (1/4) * (f y) * (f z) - (1/4) * (f x) * (f z) := by
  obtain ⟨h0|h0, h1|h1, h2|h2⟩ := And.intro (hbv.one_or_neg_one x)
    (And.intro (hbv.one_or_neg_one y) (hbv.one_or_neg_one z)) <;>
      { rw [h0, h1, h2]; norm_num }
end BooleanFun.BV
