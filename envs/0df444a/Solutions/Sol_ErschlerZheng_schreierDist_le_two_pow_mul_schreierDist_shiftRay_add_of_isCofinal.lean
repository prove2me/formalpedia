-- Prove2me | solution 1 for ErschlerZheng.schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:49:16.842781+00:00
-- url     : https://prove2.me/submissions/8b9c7c08-f1b2-4c34-8849-1ffddca33ae4

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

theorem AllOnesFrom.mono {N M : ℕ} {x : Ray} (h : AllOnesFrom N x) (hNM : N ≤ M) :
    AllOnesFrom M x := fun k hk => h k (le_trans hNM hk)

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

theorem grayList_append (u v : List Bool) :
    ∃ r < 2 ^ u.length, grayList (u ++ v) = r + 2 ^ u.length * grayList v := by
  induction u with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons b u ih =>
    obtain ⟨r, hr, he⟩ := ih
    refine ⟨(b :: (u ++ v)).count false % 2 + 2 * r, ?_, ?_⟩
    · rw [List.length_cons, pow_succ]
      have : (b :: (u ++ v)).count false % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    · rw [List.cons_append, grayList_cons, he, List.length_cons, pow_succ]
      ring

theorem isCofinal_shiftRay {x : Ray} (hx : IsCofinal x) (n : ℕ) : IsCofinal (shiftRay x n) :=
  (Filter.tendsto_add_atTop_nat n).eventually hx

theorem allOnesFrom_shiftRay {N : ℕ} {x : Ray} (h : AllOnesFrom N x) (n : ℕ) :
    AllOnesFrom N (shiftRay x n) := fun k hk => h (k + n) (by omega)

/-- `x̄ = r + 2ⁿ (𝔰ⁿx)‾` with `r < 2ⁿ`. -/
theorem grayCode_split {x : Ray} (hx : IsCofinal x) (n : ℕ) :
    ∃ r < 2 ^ n, grayCode x = r + 2 ^ n * grayCode (shiftRay x n) := by
  obtain ⟨N, hN⟩ := (isCofinal_iff x).mp hx
  have h1 : AllOnesFrom (n + N) x := hN.mono (by omega)
  rw [grayCode_eq h1, grayCode_eq (allOnesFrom_shiftRay hN n), rayPrefix_add]
  have := grayList_append (rayPrefix x n) (rayPrefix (shiftRay x n) N)
  rwa [length_rayPrefix] at this

end Fact73Dev

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open Fact73Dev SchreierDev in
theorem solution (ω : ℕ → Fin 3)
    (x y : Ray) (hx : IsCofinal x) (hy : IsCofinal y) (n : ℕ) :
    schreierDist ω x y ≤ 2 ^ n * schreierDist ω (shiftRay x n) (shiftRay y n) + 2 ^ n - 1 := by
  have h1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x y hx hy
  have h2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω (shiftRay x n) (shiftRay y n)
    (isCofinal_shiftRay hx n) (isCofinal_shiftRay hy n)
  obtain ⟨rx, hrx, ex⟩ := grayCode_split hx n
  obtain ⟨ry, hry, ey⟩ := grayCode_split hy n
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  suffices H : (schreierDist ω x y : ℤ) ≤
      2 ^ n * schreierDist ω (shiftRay x n) (shiftRay y n) + 2 ^ n - 1 by
    have : ((2 ^ n * schreierDist ω (shiftRay x n) (shiftRay y n) + 2 ^ n - 1 : ℕ) : ℤ) =
        2 ^ n * schreierDist ω (shiftRay x n) (shiftRay y n) + 2 ^ n - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    exact_mod_cast (this ▸ H)
  rw [h1, h2, ex, ey]
  push_cast
  have hr : |(rx : ℤ) - ry| ≤ 2 ^ n - 1 := by
    rw [abs_le]; constructor <;>
    · have : (rx : ℤ) < 2 ^ n := by exact_mod_cast hrx
      have : (ry : ℤ) < 2 ^ n := by exact_mod_cast hry
      have : (0 : ℤ) ≤ rx := by positivity
      have : (0 : ℤ) ≤ ry := by positivity
      linarith
  have hpos : (0 : ℤ) ≤ 2 ^ n := by positivity
  calc |(rx : ℤ) + 2 ^ n * grayCode (shiftRay x n) - (ry + 2 ^ n * grayCode (shiftRay y n))|
      = |((rx : ℤ) - ry) + 2 ^ n * (grayCode (shiftRay x n) - grayCode (shiftRay y n))| := by
        ring_nf
    _ ≤ |(rx : ℤ) - ry| + |2 ^ n * ((grayCode (shiftRay x n) : ℤ) - grayCode (shiftRay y n))| :=
        abs_add_le _ _
    _ = |(rx : ℤ) - ry| + 2 ^ n * |(grayCode (shiftRay x n) : ℤ) - grayCode (shiftRay y n)| := by
        rw [abs_mul, abs_of_nonneg hpos]
    _ ≤ 2 ^ n * |(grayCode (shiftRay x n) : ℤ) - grayCode (shiftRay y n)| + 2 ^ n - 1 := by
        linarith
end
