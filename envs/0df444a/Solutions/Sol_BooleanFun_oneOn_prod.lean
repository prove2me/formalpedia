-- Prove2me | solution 1 for BooleanFun.oneOn_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:08.877714+00:00
-- url     : https://prove2.me/submissions/fee7067b-bfe6-4bac-88f2-b20768b624f9

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
noncomputable section
variable {p q : Prop}
open Classical
namespace BooleanFun
theorem _root_.solution {p : ι → Prop} : ∏ i, oneOn (p i) = oneOn (∀ i, p i) := by
  unfold oneOn
  split_ifs with h
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [← Finset.prod_erase_mul (a := i) (s := Finset.univ) (h := Finset.mem_univ i)]
    simp [hi]
end BooleanFun
