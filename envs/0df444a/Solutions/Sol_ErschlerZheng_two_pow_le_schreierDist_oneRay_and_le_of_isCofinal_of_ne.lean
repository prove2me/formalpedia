-- Prove2me | solution 1 for ErschlerZheng.two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:28:45.499967+00:00
-- url     : https://prove2.me/submissions/4464a27f-979c-48a6-806c-bb9f9a87941a

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal

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

/-! ### The root swap -/

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

theorem rayPrefix_add (x : Ray) (n m : ℕ) :
    rayPrefix x (n + m) = rayPrefix x n ++ rayPrefix (shiftRay x n) m := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    by_cases hi : i < n
    · rw [List.getElem_append_left (by rw [length_rayPrefix]; exact hi), getElem_rayPrefix]
    · rw [List.getElem_append_right (by rw [length_rayPrefix]; omega), getElem_rayPrefix]
      simp only [shiftRay, length_rayPrefix]
      congr 1
      omega

end RayBasic

end ErschlerZheng
end

section
/-!
# The Gray code on finite words, and how the generators move it

For a word `w` of length `N`, `grayList w < 2^N`. The generator `a` changes it by `+1` when `w`
has an even number of zeros and by `-1` otherwise; a generator `γ_ω` either fixes `w` or changes
it by `-1` (even) or `+1` (odd). From every word there is a generator step up (below the top
value `2^N - 1`) and down (above `0`) whose section at `w` is trivial.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace GrayDev

open GrigBasic

theorem grayList_cons (b : Bool) (v : List Bool) :
    grayList (b :: v) = (b :: v).count false % 2 + 2 * grayList v := rfl

theorem grayList_lt (w : List Bool) : grayList w < 2 ^ w.length := by
  induction w with
  | nil => simp [grayList]
  | cons b v ih =>
    rw [grayList_cons, List.length_cons, pow_succ]
    have : (b :: v).count false % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

theorem grayList_append_true (w : List Bool) : grayList (w ++ [true]) = grayList w := by
  induction w with
  | nil => simp [grayList]
  | cons b v ih =>
    rw [List.cons_append, grayList_cons, grayList_cons, ih]
    simp [List.count_cons, List.count_append]

theorem grayList_append_replicate (w : List Bool) (m : ℕ) :
    grayList (w ++ List.replicate m true) = grayList w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, grayList_append_true, ih]

end GrayDev

end ErschlerZheng
end

section
/-!
# The Schreier graph of `1^∞` through the Gray code

Rays that are all ones from position `N` on are `prepend w 1^∞` with `|w| = N`; their Gray code
is `grayList w`. A generator moves the Gray code of such a ray by at most one, and from `w` to
`w'` of the same length there is a path of `|ḡ(w) - ḡ(w')|` generators with trivial sections at
the intermediate words, so it carries any tail along unchanged.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierDev

open GrigBasic RayBasic GrayDev

/-- `x_k = 1` for every `k ⩾ N`. -/
def AllOnesFrom (N : ℕ) (x : Ray) : Prop := ∀ k ≥ N, x k = true

theorem isCofinal_iff (x : Ray) : IsCofinal x ↔ ∃ N, AllOnesFrom N x :=
  Filter.eventually_atTop

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

theorem shiftRay_eq_oneRay {N : ℕ} {x : Ray} (h : AllOnesFrom N x) : shiftRay x N = oneRay := by
  funext i; simp only [shiftRay, oneRay]; exact h _ (by omega)

theorem grayCode_eq {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    grayCode x = grayList (rayPrefix x N) := by
  unfold grayCode
  set M := maxZeroIndex x with hM
  have hMdef : M = sSup {k | 1 ≤ k ∧ x (k - 1) = false} := rfl
  have hbdd : ∀ k ∈ {k | 1 ≤ k ∧ x (k - 1) = false}, k ≤ N := by
    rintro k ⟨hk1, hk⟩
    by_contra hc
    have := h (k - 1) (by omega)
    rw [this] at hk
    exact Bool.noConfusion hk
  have hMN : M ≤ N := csSup_le' hbdd
  have hones : AllOnesFrom M x := by
    intro k hk
    by_contra hc
    have hmem : k + 1 ∈ {k | 1 ≤ k ∧ x (k - 1) = false} := by
      refine ⟨by omega, ?_⟩
      simpa using hc
    have := le_csSup ⟨N, hbdd⟩ hmem
    rw [← hMdef] at this
    omega
  have hsplit : rayPrefix x N = rayPrefix x M ++ List.replicate (N - M) true := by
    rw [show N = M + (N - M) by omega, rayPrefix_add, shiftRay_eq_oneRay hones,
      rayPrefix_oneRay]
    simp
  rw [hsplit, grayList_append_replicate]

theorem grayCode_oneRay : grayCode oneRay = 0 := by
  rw [grayCode_eq (N := 0) (x := oneRay) (fun k _ => rfl)]
  rfl

/-! ### Generators on rays that are eventually all ones -/

end SchreierDev

end ErschlerZheng
end

section
/-!
# A10 (Fact 7.3) and A11 (Fact 7.4), p. 35, from A9 (`d_𝒮(x, y) = |x̄ - ȳ|`)
-/

open scoped RightActions

namespace ErschlerZheng

namespace Fact73Dev

open GrigBasic RayBasic GrayDev SchreierDev

theorem grayList_append_false (u : List Bool) : 2 ^ u.length ≤ grayList (u ++ [false]) := by
  induction u with
  | nil => simp [grayList]
  | cons b u ih =>
    rw [List.cons_append, grayList_cons, List.length_cons, pow_succ]
    omega

end Fact73Dev

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open Fact73Dev SchreierDev RayBasic GrayDev in
theorem solution (ω : ℕ → Fin 3) (x : Ray)
    (hx : IsCofinal x) (hxo : x ≠ oneRay) :
    2 ^ (maxZeroIndex x - 1) ≤ schreierDist ω x oneRay ∧
      schreierDist ω x oneRay ≤ 2 ^ maxZeroIndex x - 1 := by
  have hd := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x oneRay hx
    (Filter.Eventually.of_forall fun _ => rfl)
  rw [grayCode_oneRay, Nat.cast_zero, sub_zero, abs_of_nonneg (by positivity)] at hd
  have hd' : schreierDist ω x oneRay = grayCode x := by exact_mod_cast hd
  rw [hd']
  -- the set of zero positions
  set S := {k | 1 ≤ k ∧ x (k - 1) = false} with hS
  have hM : maxZeroIndex x = sSup S := rfl
  obtain ⟨N, hN⟩ := (isCofinal_iff x).mp hx
  have hbdd : BddAbove S := by
    refine ⟨N, ?_⟩
    rintro k ⟨hk1, hk⟩
    by_contra hc
    have := hN (k - 1) (by omega)
    rw [this] at hk
    exact Bool.noConfusion hk
  have hne : S.Nonempty := by
    by_contra hemp
    apply hxo
    funext k
    by_contra hk
    apply hemp
    refine ⟨k + 1, by omega, ?_⟩
    simpa [oneRay] using hk
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  rw [← hM] at hmem
  obtain ⟨hM1, hMx⟩ := hmem
  unfold grayCode
  have hsplit : rayPrefix x (maxZeroIndex x) = rayPrefix x (maxZeroIndex x - 1) ++ [false] := by
    conv_lhs => rw [show maxZeroIndex x = maxZeroIndex x - 1 + 1 by omega]
    rw [rayPrefix_add]
    simp [rayPrefix, shiftRay, hMx]
  constructor
  · rw [hsplit]
    have := grayList_append_false (rayPrefix x (maxZeroIndex x - 1))
    rwa [length_rayPrefix] at this
  · have := grayList_lt (rayPrefix x (maxZeroIndex x))
    rw [length_rayPrefix] at this
    omega
end
