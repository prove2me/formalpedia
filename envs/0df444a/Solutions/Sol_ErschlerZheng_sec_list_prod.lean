-- Prove2me | solution 1 for ErschlerZheng.sec_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T00:48:25.500201+00:00
-- url     : https://prove2.me/submissions/88e10497-af10-41ae-b5e8-80243f66afb7

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_mul (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  apply sec_unique
  intro w
  rw [vertex_smul_mul, vertex_smul_mul, append_vertex_smul, append_vertex_smul,
    vertex_smul_mul]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# A4: the chain rule for sections, (7.17) p. 54
-/

open scoped RightActions

namespace ErschlerZheng

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
theorem solution (l : List Garrido.BinaryTreeAut) (z : List Bool) :
    sec l.prod z = (List.ofFn fun i : Fin l.length => sec l[i] (z <• (l.take i).prod)).prod := by
  induction l generalizing z with
  | nil => simp [GrigBasic.sec_one]
  | cons g l ih =>
    rw [List.prod_cons, GrigBasic.sec_mul, ih]
    simp only [List.length_cons, List.ofFn_succ, List.prod_cons, Fin.val_zero,
      List.take_zero, List.prod_nil, Fin.val_succ,
      List.take_succ_cons, vertex_smul_mul]
    rfl
end
