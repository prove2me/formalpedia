-- Prove2me | solution 1 for ErschlerZheng.not_forall_evalWord_zetaWord_congr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.808678+00:00
-- url     : https://prove2.me/submissions/329d900a-9212-4a1a-9d96-5583c95027fc

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# A7F: the printed claim of p. 15 fails for `ω = 1 0^∞`, `n = 0`

In `G_{0^∞}`, `b = c`, so the words `ab` and `ac` agree; but `ζ_1(ab) = abab` fixes level 1 while
`ζ_1(ac) = adacab` swaps it.
-/

open scoped RightActions

namespace ErschlerZheng

namespace A7FDev

theorem genFun_zero_b_eq_c (w : List Bool) :
    genFun (fun _ => 0) .b w = genFun (fun _ => 0) .c w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    cases x
    · rfl
    · show true :: genFun (shiftSeq (fun _ => 0) 1) .b w =
        true :: genFun (shiftSeq (fun _ => 0) 1) .c w
      have : shiftSeq (fun _ : ℕ => (0 : Fin 3)) 1 = fun _ => 0 := rfl
      rw [this, ih]

end A7FDev

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open A7FDev in
theorem solution :
    ¬ ∀ (ω : ℕ → Fin 3) (n : ℕ) (w₁ w₂ : List APair),
      evalWord ω (n + 1) (w₁.flatMap APair.toWord) = evalWord ω (n + 1) (w₂.flatMap APair.toWord) →
        evalWord ω n ((zetaWord (ω n) w₁).flatMap APair.toWord) =
          evalWord ω n ((zetaWord (ω n) w₂).flatMap APair.toWord) := by
  intro h
  let ω : ℕ → Fin 3 := fun k => if k = 0 then 1 else 0
  have hs : shiftSeq ω (0 + 1) = fun _ => 0 := by
    funext k; simp [shiftSeq, ω]
  have hbc : gen (shiftSeq ω (0 + 1)) .b = gen (shiftSeq ω (0 + 1)) .c := by
    rw [hs]; apply Subtype.ext; apply Equiv.ext; intro w; exact genFun_zero_b_eq_c w
  have key := h ω 0 [.ab] [.ac] (by
    simp only [List.flatMap_cons, List.flatMap_nil, APair.toWord, List.append_nil, evalWord,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hbc])
  have := congrArg (fun g => [false] <• g) key
  revert this
  decide
end
