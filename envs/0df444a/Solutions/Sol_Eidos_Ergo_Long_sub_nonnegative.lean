-- Prove2me | solution 1 for Eidos.Ergo.Long.sub_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:02.55045+00:00
-- url     : https://prove2.me/submissions/fde1d073-75b2-4ccc-ac15-05953de3148b

import Std
import Definitions.Def_Eidos_Ergo_Long
import Theorems.Thm_Eidos_Ergo_Long_sub_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.sub_eq_ok_iff

set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long
namespace Eidos.Ergo.Long
theorem _root_.solution (x y : Long) (hy : 0 ≤ y.val) (hxy : y.val ≤ x.val) :
    ∃ z, sub x y = .ok z ∧ z.val = x.val - y.val ∧ 0 ≤ z.val := by
  have hx := x.property
  have hr : -9223372036854775808 ≤ x.val - y.val ∧
      x.val - y.val ≤ 9223372036854775807 := by omega
  exact ⟨⟨x.val - y.val, hr⟩, (sub_eq_ok_iff _ _ _).2 rfl, rfl,
    show 0 ≤ x.val - y.val from by omega⟩
end Eidos.Ergo.Long
