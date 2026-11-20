-- Prove2me | solution 1 for BooleanFun.BV.oneOn_eq_of_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:11:19.138632+00:00
-- url     : https://prove2.me/submissions/c7b99df8-e561-4c0a-a740-3c87a2d35c10

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
    oneOn (x = y) = (1/2) * (1 + x * y) := by
  obtain ⟨hx|hx, hy|hy⟩ := And.intro hx hy <;> { rw [hx, hy]; norm_num }
end BooleanFun.BV
