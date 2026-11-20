-- Prove2me | solution 1 for BooleanFun.BV.oneOn_ne_of_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:22.96773+00:00
-- url     : https://prove2.me/submissions/224fb1cd-1c03-4c25-81b1-6b51f799be1a

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1):
    oneOn (x ≠ y) = (1/2) * (1-x * y) := by
  obtain ⟨hx|hx, hy|hy⟩ := And.intro hx hy <;> { rw [hx, hy]; norm_num }
end BooleanFun.BV
