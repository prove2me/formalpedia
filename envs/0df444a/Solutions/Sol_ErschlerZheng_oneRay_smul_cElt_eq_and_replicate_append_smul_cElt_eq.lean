-- Prove2me | solution 1 for ErschlerZheng.oneRay_smul_cElt_eq_and_replicate_append_smul_cElt_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T05:11:11.37668+00:00
-- url     : https://prove2.me/submissions/db21bd34-44c5-49c2-a5b6-7b772ba6b49a

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_smul_cElt_eq_self_and_sec_cElt_eq

section
/-!
# The index sets `W^n_k` and `V^j_k` (Erschler–Zheng p. 37)

`|W^n_k| = 2^{k/D}` for `D ∣ n`, `D ∣ k`; `|V^j_k| = 2^{k/D}` and every `v ∈ V^j_k` ends with `0`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrW

end ConstrW

end ErschlerZheng
end

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

/-- Whether `g` swaps the two vertices of level 1. -/
def rootSwap (g : BinaryTreeAut) : Bool := decide ([false] <• g = [true])

theorem singleton_smul (g : BinaryTreeAut) (x : Bool) :
    [x] <• g = [xor x (rootSwap g)] := by
  have hlen : ∀ y : Bool, ([y] <• g).length = 1 := fun y => length_vertex_smul g [y]
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp (hlen false)
  obtain ⟨q, hq⟩ := List.length_eq_one_iff.mp (hlen true)
  have hne : p ≠ q := by
    intro e
    have : [false] <• g = [true] <• g := by rw [hp, hq, e]
    have := congrArg (fun v => v <• g⁻¹) this
    simp only [vertex_smul_smul_inv] at this
    simp at this
  unfold rootSwap
  cases x
  · rw [hp]
    cases p <;> simp
  · rw [hq, hp]
    cases p <;> cases q <;> simp_all

/-! ### `a` and the generators -/

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Root swap and level-1 sections of products (helpers for A5, A7)
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ZetaDev

open GrigBasic

end ZetaDev

end ErschlerZheng
end

section
/-!
# Fact 7.6: `ι([γ_{𝔰ⁿω}, a], v)` lies in `G_ω`, with word length at most `2^{n+2}`

The words of the paper's proof (p. 37), built from the bottom: a word `w` read in `G_{𝔰^{ℓ+1}ω}`
is lifted to `G_{𝔰^ℓ ω}` letter by letter, by `a ↦ a y a`, `γ ↦ γ` (to act below `1`) or by
`a ↦ y`, `γ ↦ a γ a` (to act below `0`), where `ω_ℓ(y) = a`. The lift acts as `w` below the chosen
vertex and as `π(w)` below the other one, where `π` sends `a ↦ y_{𝔰^{ℓ+1}ω}`, `γ ↦ ω_ℓ(γ)`.
The invariant that makes `π(w) = 1` is `Kill`: `w` evaluates to `1` under every letter map
`a ↦ z`, `γ ↦ (A if ω_ℓ(γ) = a, else 1)` with `z, A` involutions.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrIota

open GrigBasic ZetaDev

/-! ### `ι` -/

/-! ### Words and letter maps -/

/-- The letter `γ` as a letter of `{a, b, c, d}`. -/
def bcdGen : BCD → Gen4
  | .b => .b
  | .c => .c
  | .d => .d

/-- The letter map `a ↦ fa`, `γ ↦ fγ γ`. -/
def lm (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : Gen4 → BinaryTreeAut
  | .a => fa
  | .b => fγ .b
  | .c => fγ .c
  | .d => fγ .d

@[simp] theorem lm_a (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .a = fa := rfl
@[simp] theorem lm_b (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .b = fγ .b := rfl
@[simp] theorem lm_c (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .c = fγ .c := rfl
@[simp] theorem lm_d (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .d = fγ .d := rfl

@[simp] theorem lm_bcdGen (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) (γ : BCD) :
    lm fa fγ (bcdGen γ) = fγ γ := by
  cases γ <;> rfl

/-! ### The lift -/


/-! ### The invariant `Kill` under lifts -/

/-! ### The words of Fact 7.6 -/

end ConstrIota

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

theorem ray_ext {x y : Ray} (h : ∀ n, rayPrefix x n = rayPrefix y n) : x = y := by
  funext i
  have hx : i < (rayPrefix x (i + 1)).length := by simp [length_rayPrefix]
  rw [← getElem_rayPrefix x (i + 1) i hx, List.getElem_of_eq (h (i + 1)), getElem_rayPrefix]

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

theorem shiftRay_smul (g : BinaryTreeAut) (x : Ray) (n : ℕ) :
    shiftRay (x <• g) n = shiftRay x n <• sec g (rayPrefix x n) := by
  apply ray_ext
  intro m
  have h1 : rayPrefix (x <• g) (n + m) =
      (rayPrefix x n <• g) ++ (rayPrefix (shiftRay x n) m <• sec g (rayPrefix x n)) := by
    rw [rayPrefix_smul, rayPrefix_add, append_vertex_smul]
  have h2 : rayPrefix (x <• g) (n + m) =
      rayPrefix (x <• g) n ++ rayPrefix (shiftRay (x <• g) n) m := rayPrefix_add _ _ _
  rw [h2, rayPrefix_smul] at h1
  rw [rayPrefix_smul]
  exact List.append_cancel_left h1

/-- `x = x_1 … x_n (𝔰ⁿ x)`. -/
theorem prepend_rayPrefix_shiftRay (x : Ray) (n : ℕ) : prepend (rayPrefix x n) (shiftRay x n) = x := by
  funext i
  unfold prepend
  split_ifs with h
  · rw [getElem_rayPrefix]
  · simp only [shiftRay, length_rayPrefix] at h ⊢
    congr 1; omega

theorem rayPrefix_prepend (u : List Bool) (x : Ray) :
    rayPrefix (prepend u x) u.length = u := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp [prepend, h2]

theorem shiftRay_prepend (u : List Bool) (x : Ray) : shiftRay (prepend u x) u.length = x := by
  funext i
  simp [shiftRay, prepend]

/-- `(v x')·g = (v·g)(x'·g_v)`. -/
theorem prepend_smul (g : BinaryTreeAut) (v : List Bool) (x : Ray) :
    prepend v x <• g = prepend (v <• g) (x <• sec g v) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay (prepend v x <• g) v.length]
  rw [rayPrefix_smul, shiftRay_smul, rayPrefix_prepend, shiftRay_prepend]

theorem one_smul_ray (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul _ x

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

/-! ### Generators on rays that are eventually all ones -/

end SchreierDev

end ErschlerZheng
end

section
/-!
# The elements `h^v_i` (7.4) (Erschler–Zheng p. 38)

For `v ∈ V^j_k`: its length, the `201`/`211` window at each digit `0`, `h^v_i` in the rigid
stabilizer of `v_1 … v_{i-2}` (Fact 7.6 for the string `𝔰^j ω`), `[b, a]` below `1`, and
`1^∞ · h^v_1 ⋯ h^v_{k'} = v 1^∞`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrH

open GrigBasic ZetaDev ConstrW ConstrIota RayBasic SchreierDev

/-! ### The positions of the digits `0` of `v ∈ V^j_k` -/

/-! ### `[b, a]` below `1` -/

/-! ### The milestone -/

theorem take_succ_eq (v : List Bool) (t : ℕ) (ht : t < v.length) :
    v.take (t + 1) = v.take t ++ [v[t]] := by
  rw [List.take_succ, List.getElem?_eq_getElem ht]
  rfl

end ConstrH

end ErschlerZheng
end

section
/-!
# Remark 7.8: `𝔠^v_j` fixes `1^∞` and every vertex `1^m 0` (Erschler–Zheng p. 39)

From Lemma 7.7: with `d` the position of the first digit `0` of `v`, `𝔠^v_j` fixes the prefixes
of `v` and their siblings, and has trivial section at `1^{d+1}`, the sibling at depth `d + 1`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrRemark78

open GrigBasic RayBasic ConstrH

theorem take_smul_of_smul_eq (g : BinaryTreeAut) (v : List Bool) (hv : v <• g = v) (i : ℕ) :
    v.take i <• g = v.take i := by
  have h := append_vertex_smul g (v.take i) (v.drop i)
  rw [List.take_append_drop, hv] at h
  have hl : (v.take i <• g).length = (v.take i).length := length_vertex_smul _ _
  have := congrArg (List.take (v.take i).length) h
  rw [List.take_left' hl] at this
  rw [← this]
  simp

theorem sibling_fixed (g : BinaryTreeAut) (p : List Bool) (x : Bool) (hp : p <• g = p)
    (hx : (p ++ [x]) <• g = p ++ [x]) (y : Bool) : (p ++ [y]) <• g = p ++ [y] := by
  rw [append_vertex_smul, hp] at hx ⊢
  have hx' := List.append_cancel_left hx
  rw [singleton_smul] at hx' ⊢
  have : rootSwap (sec g p) = false := by
    cases h : rootSwap (sec g p) <;> simp_all
  rw [this]
  simp

end ConstrRemark78

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrRemark78
open GrigBasic RayBasic ConstrH
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) :
    oneRay <• cElt ω j v = oneRay ∧
      ∀ m : ℕ, (List.replicate m true ++ [false]) <• cElt ω j v =
        List.replicate m true ++ [false] := by
  obtain ⟨hfix, hsib, -, -⟩ := smul_cElt_eq_self_and_sec_cElt_eq D ω hω j k hk v hv
  set c := cElt ω j v
  classical
  have hex : ∃ d, ∃ h : d < v.length, v[d] = false := by
    obtain ⟨u, -, rfl⟩ := hv
    refine ⟨(List.replicate (D - j % D) true ++ u ++
      List.replicate (frM D ω (ellIndex D k j) + 2) true).length, by simp, ?_⟩
    rw [List.getElem_append_right (le_refl _)]
    simp
  let d := Nat.find hex
  obtain ⟨hd, hvd⟩ := Nat.find_spec hex
  have hbefore : ∀ i (hi : i < d), v[i]'(by omega) = true := by
    intro i hi
    have := Nat.find_min hex hi
    simp only [not_exists] at this
    cases h : v[i]'(by omega)
    · exact absurd h (this (by omega))
    · rfl
  have htake : v.take d = List.replicate d true := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_replicate]
      exact hbefore i (by simpa using h2)
  -- the vertex `1^{d+1}`: fixed, with trivial section
  have hfixtake : ∀ i, v.take i <• c = v.take i := take_smul_of_smul_eq c v hfix
  have hsucc : v.take (d + 1) = v.take d ++ [false] := by
    rw [take_succ_eq v d hd, hvd]
  have hU : (List.replicate (d + 1) true) <• c = List.replicate (d + 1) true := by
    have := sibling_fixed c (v.take d) false (hfixtake d) (by rw [← hsucc]; exact hfixtake _) true
    rwa [htake, ← List.replicate_succ'] at this
  have hsecU : sec c (List.replicate (d + 1) true) = 1 := by
    have := hsib d hd (by intro h; rw [hvd] at h; exact absurd h (by simp))
    rwa [hvd, Bool.not_false, htake, ← List.replicate_succ'] at this
  refine ⟨?_, fun m => ?_⟩
  · have e : oneRay = prepend (List.replicate (d + 1) true) oneRay := by
      funext i; simp [prepend, oneRay]
    rw [e, prepend_smul, hU, hsecU, one_smul_ray]
  · rcases Nat.lt_trichotomy m d with hm | rfl | hm
    · -- a sibling of the path `v`
      have h1 : v.take m = List.replicate m true := by
        have := congrArg (List.take m) htake
        rw [List.take_take, min_eq_left (le_of_lt hm)] at this
        rw [this]
        simp [List.take_replicate, min_eq_left (le_of_lt hm)]
      have h2 : v.take (m + 1) = v.take m ++ [true] := by
        rw [take_succ_eq v m (by omega), hbefore m hm]
      have := sibling_fixed c (v.take m) true (hfixtake m) (by rw [← h2]; exact hfixtake _) false
      rwa [h1] at this
    · rw [← htake, ← hsucc]; exact hfixtake _
    · have e : List.replicate m true ++ [false] =
          List.replicate (d + 1) true ++ (List.replicate (m - (d + 1)) true ++ [false]) := by
        rw [← List.append_assoc, ← List.replicate_add]
        congr 2
        omega
      rw [e, append_vertex_smul, hU, hsecU]
      rfl
end
