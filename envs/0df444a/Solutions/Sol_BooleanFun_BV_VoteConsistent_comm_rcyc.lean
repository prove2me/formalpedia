-- Prove2me | solution 1 for BooleanFun.BV.VoteConsistent.comm_rcyc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:12:24.763043+00:00
-- url     : https://prove2.me/submissions/46790a1d-aefc-45d5-a853-e76f9639f662

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
namespace VoteConsistent
theorem _root_.solution {x y z : Votes n}:
    VoteConsistent x y z = VoteConsistent y z x := by
  apply propext
  constructor <;> { intro h i; specialize h i; push Not; intro h'; rw [h'] at h; tauto }
end VoteConsistent
end BooleanFun.BV
