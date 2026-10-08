-- Prove2me | solution 1 for ErschlerZheng.orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:28:45.596082+00:00
-- url     : https://prove2.me/submissions/d0af0150-b77e-4d74-a783-eebb460f8766

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary

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

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

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

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem rootSwap_grigA : rootSwap grigA = true := by
  unfold rootSwap
  rw [vertex_smul_grigA]
  rfl

theorem sec_grigA (x : Bool) : sec grigA [x] = 1 := by
  apply sec_unique
  intro w
  rw [vertex_smul_grigA, vertex_smul_grigA]
  rfl

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

theorem vertex_smul_gen (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    v <• gen ω γ = genFun ω γ v := by
  rw [vertex_smul_def, gen_inv]
  rfl

/-- The element `ω_0(γ) ∈ {a, id}`. -/
def letterElt (i : Fin 3) (γ : BCD) : BinaryTreeAut := if letterValue i γ then grigA else 1

theorem sec_gen_false (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [false] = letterElt (ω 0) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen]
  unfold letterElt
  by_cases h : letterValue (ω 0) γ
  · simp only [List.cons_append, List.nil_append, genFun, h, if_true]
    rw [vertex_smul_grigA]
    rfl
  · simp only [List.cons_append, List.nil_append, genFun, h]
    rfl

theorem sec_gen_true (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [true] = gen (shiftSeq ω 1) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen, vertex_smul_gen]
  simp [genFun]

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

theorem singleton_rayPrefix (x : Ray) : rayPrefix x 1 = [x 0] := by
  simp [rayPrefix]

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

theorem genFun_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) :
    genFun ω γ (List.replicate k true ++ false :: z) =
      List.replicate k true ++ false :: (if letterValue (ω k) γ then grigAFun z else z) := by
  induction k generalizing ω with
  | zero => simp [genFun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, genFun, ih]
    simp only [shiftSeq]
    rfl

/-- A letter `γ` with `ω_k(γ) = a`. -/
theorem exists_letterValue (i : Fin 3) : ∃ γ : BCD, letterValue i γ = true := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by
    rcases i with ⟨k, hk⟩; interval_cases k <;> simp) with h | h | h <;> subst h
  · exact ⟨.b, by decide⟩
  · exact ⟨.b, by decide⟩
  · exact ⟨.c, by decide⟩

theorem grigA_mem_gens (ω : ℕ → Fin 3) : grigA ∈ gens ω := by simp [gens]

theorem gen_mem_gens (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ gens ω := by
  cases γ <;> simp [gens]

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

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

/-! ### Generators on rays that are eventually all ones -/

theorem genFun_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    genFun ω γ (List.replicate n true) = List.replicate n true := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, genFun, ih]

theorem oneRay_smul_gen (ω : ℕ → Fin 3) (γ : BCD) : oneRay <• gen ω γ = oneRay := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, rayPrefix_oneRay, vertex_smul_gen, genFun_replicate_true]

theorem gens_involutive (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) : s⁻¹ = s := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact grigA_inv
  all_goals exact gen_inv _ _

theorem mem_gens_of_inv_mem (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s⁻¹ ∈ gens ω) :
    s ∈ gens ω := by
  have := gens_involutive ω hs
  rw [inv_inv] at this
  rw [this]; exact hs

theorem ray_smul_list_cons (x : Ray) (s : BinaryTreeAut) (l : List BinaryTreeAut) :
    x <• (s :: l).prod = (x <• s) <• l.prod := by
  rw [List.prod_cons, MulOpposite.op_mul, mul_smul]

end SchreierDev

end ErschlerZheng
end

section
/-!
# A8: the Schreier graph of `1^∞` does not depend on `ω` (p. 34)

The orbit is the cofinality class of `1^∞` for every `ω` (A2). For every ray `x`, the neighbours
`x·s`, `s ∈ S`, are `x·a`, `x` itself and `F(x)`, the ray with the digit after the first `0`
flipped (`x` itself if `x = 1^∞`): each `γ_ω` acts on `x` as `ω_k(γ) ∈ {a, id}` on the digit after
the first zero `x_k`, and among `b, c, d` one is killed by `ω_k` and two are not. Paths of
generators for `ω` are then paths for `ω'` of the same length.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierIndepDev

open GrigBasic RayBasic GrayDev SchreierDev

theorem sec_gen_replicate_false (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) :
    sec (gen ω γ) (List.replicate k true ++ [false]) = letterElt (ω k) γ := by
  induction k generalizing ω with
  | zero => simp [sec_gen_false]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sec_cons, sec_gen_true, ih]
    simp [shiftSeq]

open Classical in
/-- The ray with the digit after the first `0` flipped. -/
noncomputable def flipAfterFirstZero (x : Ray) : Ray :=
  if h : ∃ k, x k = false then fun i => if i = Nat.find h + 1 then !x i else x i else x

theorem rayPrefix_first_zero (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true) :
    rayPrefix x (k + 1) = List.replicate k true ++ [false] := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp only [length_rayPrefix] at h1
    by_cases hi : i < k
    · rw [List.getElem_append_left (by simpa using hi)]; simp [hmin i hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      have : i = k := by omega
      subst this; simp [hk]

theorem grigA_smul_ray (x : Ray) : x <• grigA = fun i => if i = 0 then !x 0 else x i := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay x 1]
  rw [prepend_smul, singleton_rayPrefix, sec_grigA, one_smul_ray, singleton_smul,
    rootSwap_grigA]
  funext i
  cases i with
  | zero => simp [prepend]
  | succ i => simp [prepend, shiftRay]

theorem gen_smul_eq (ω : ℕ → Fin 3) (γ : BCD) (x : Ray) :
    x <• gen ω γ = x ∨ x <• gen ω γ = flipAfterFirstZero x := by
  classical
  by_cases hz : ∃ k, x k = false
  · set k := Nat.find hz
    have hk : x k = false := Nat.find_spec hz
    have hmin : ∀ j < k, x j = true := fun j hj => by
      have := Nat.find_min hz hj; simpa using this
    have hpre := rayPrefix_first_zero x k hk hmin
    have hx : x <• gen ω γ =
        prepend (rayPrefix x (k + 1)) (shiftRay x (k + 1) <• letterElt (ω k) γ) := by
      conv_lhs => rw [← prepend_rayPrefix_shiftRay x (k + 1)]
      rw [prepend_smul, hpre, sec_gen_replicate_false, vertex_smul_gen, genFun_replicate]
      simp [grigAFun]
    unfold letterElt at hx
    split_ifs at hx with hl
    · right
      rw [hx, grigA_smul_ray]
      unfold flipAfterFirstZero
      rw [dif_pos hz]
      funext i
      simp only [prepend, length_rayPrefix, shiftRay]
      by_cases hi : i < k + 1
      · rw [dif_pos hi, getElem_rayPrefix, if_neg (by omega)]
      · rw [dif_neg hi]
        by_cases hi' : i = k + 1
        · subst hi'; simp [k]
        · rw [if_neg (by omega), if_neg hi']; congr 1; omega
    · left
      rw [hx, one_smul_ray, prepend_rayPrefix_shiftRay]
  · left
    push Not at hz
    have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
    rw [hx, oneRay_smul_gen]

theorem exists_gen_smul_eq_self (ω : ℕ → Fin 3) (x : Ray) : ∃ γ, x <• gen ω γ = x := by
  classical
  by_cases hz : ∃ k, x k = false
  · obtain ⟨k, hk, hmin⟩ : ∃ k, x k = false ∧ ∀ j < k, x j = true :=
      ⟨Nat.find hz, Nat.find_spec hz, fun j hj => by simpa using Nat.find_min hz hj⟩
    refine ⟨BCD.killedBy (ω k), ?_⟩
    have hpre := rayPrefix_first_zero x k hk hmin
    conv_lhs => rw [← prepend_rayPrefix_shiftRay x (k + 1)]
    rw [prepend_smul, hpre, sec_gen_replicate_false, vertex_smul_gen, genFun_replicate]
    have : letterValue (ω k) (BCD.killedBy (ω k)) = false := by simp [letterValue]
    simp only [this, letterElt, Bool.false_eq_true, if_false, one_smul_ray]
    rw [← hpre, prepend_rayPrefix_shiftRay]
  · push Not at hz
    have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
    exact ⟨.b, by rw [hx, oneRay_smul_gen]⟩

theorem exists_gen_smul_eq_flip (ω : ℕ → Fin 3) (x : Ray) :
    ∃ γ, x <• gen ω γ = flipAfterFirstZero x := by
  classical
  by_cases hz : ∃ k, x k = false
  · obtain ⟨γ, hγ⟩ := exists_letterValue (ω (Nat.find hz))
    refine ⟨γ, ?_⟩
    rcases gen_smul_eq ω γ x with h | h
    · exfalso
      have hk : x (Nat.find hz) = false := Nat.find_spec hz
      have hmin : ∀ j < Nat.find hz, x j = true := fun j hj => by
        have := Nat.find_min hz hj; simpa using this
      have hpre := rayPrefix_first_zero x _ hk hmin
      have h2 : x <• gen ω γ =
          prepend (rayPrefix x (Nat.find hz + 1)) (shiftRay x (Nat.find hz + 1) <• grigA) := by
        conv_lhs => rw [← prepend_rayPrefix_shiftRay x (Nat.find hz + 1)]
        rw [prepend_smul, hpre, sec_gen_replicate_false, vertex_smul_gen, genFun_replicate]
        simp [grigAFun, letterElt, hγ]
      rw [h] at h2
      have := congrFun h2 (Nat.find hz + 1)
      simp [prepend, length_rayPrefix, grigA_smul_ray, shiftRay] at this
    · exact h
  · push Not at hz
    have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
    refine ⟨.b, ?_⟩
    rw [hx, oneRay_smul_gen]
    unfold flipAfterFirstZero
    rw [dif_neg (by simp [oneRay])]

theorem neighbours_iff (ω : ℕ → Fin 3) (x y : Ray) :
    (∃ s ∈ gens ω, y = x <• s) ↔ y = x <• grigA ∨ y = x ∨ y = flipAfterFirstZero x := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · left; rfl
    all_goals
      right
      rcases gen_smul_eq ω _ x with h | h
      · left; exact h
      · right; exact h
  · rintro (rfl | rfl | rfl)
    · exact ⟨grigA, grigA_mem_gens ω, rfl⟩
    · obtain ⟨γ, hγ⟩ := exists_gen_smul_eq_self ω y
      exact ⟨gen ω γ, gen_mem_gens ω γ, hγ.symm⟩
    · obtain ⟨γ, hγ⟩ := exists_gen_smul_eq_flip ω x
      exact ⟨gen ω γ, gen_mem_gens ω γ, hγ.symm⟩

theorem adjacent_iff (ω ω' : ℕ → Fin 3) (x y : Ray) :
    (∃ s ∈ gens ω, y = x <• s) ↔ ∃ s ∈ gens ω', y = x <• s := by
  rw [neighbours_iff, neighbours_iff]

theorem transfer (ω ω' : ℕ → Fin 3) :
    ∀ (l : List BinaryTreeAut), (∀ s ∈ l, s ∈ gens ω) → ∀ x : Ray,
      ∃ l' : List BinaryTreeAut, l'.length = l.length ∧ (∀ s ∈ l', s ∈ gens ω') ∧
        x <• l'.prod = x <• l.prod
  | [], _, x => ⟨[], rfl, by simp, rfl⟩
  | s :: l, hl, x => by
    obtain ⟨s', hs', he⟩ := (adjacent_iff ω ω' x (x <• s)).mp ⟨s, hl s (by simp), rfl⟩
    obtain ⟨l', hlen, hl', hp⟩ := transfer ω ω' l (fun t ht => hl t (by simp [ht])) (x <• s)
    refine ⟨s' :: l', by simp [hlen], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hs'
      · exact hl' t ht
    · rw [ray_smul_list_cons, ray_smul_list_cons, ← he, hp]

theorem reach_iff (ω ω' : ℕ → Fin 3) (x y : Ray) (n : ℕ) :
    (∃ g ∈ Chou.wordBall (gens ω) n, y = x <• g) → ∃ g ∈ Chou.wordBall (gens ω') n, y = x <• g := by
  rintro ⟨g, ⟨l, hlen, hls, rfl⟩, rfl⟩
  have hls' : ∀ s ∈ l, s ∈ gens ω := fun s hs => by
    rcases hls s hs with h | h
    · exact h
    · exact mem_gens_of_inv_mem ω h
  obtain ⟨l', hlen', hl', hp⟩ := transfer ω ω' l hls' x
  exact ⟨l'.prod, ⟨l', by omega, fun s hs => Or.inl (hl' s hs), rfl⟩, hp.symm⟩

/-- On a ray with a digit `0`, `γ_ω` flips the digit after the first `0` exactly when the letter
`ω_k` at that first `0` does not kill `γ`. -/
theorem gen_smul_eq_ite (ω : ℕ → Fin 3) (γ : BCD) (x : Ray) (hz : ∃ k, x k = false) :
    x <• gen ω γ = if letterValue (ω (Nat.find hz)) γ then flipAfterFirstZero x else x := by
  classical
  set k := Nat.find hz
  have hk : x k = false := Nat.find_spec hz
  have hmin : ∀ j < k, x j = true := fun j hj => by
    have := Nat.find_min hz hj; simpa using this
  have hpre := rayPrefix_first_zero x k hk hmin
  have hx : x <• gen ω γ =
      prepend (rayPrefix x (k + 1)) (shiftRay x (k + 1) <• letterElt (ω k) γ) := by
    conv_lhs => rw [← prepend_rayPrefix_shiftRay x (k + 1)]
    rw [prepend_smul, hpre, sec_gen_replicate_false, vertex_smul_gen, genFun_replicate]
    simp [grigAFun]
  unfold letterElt at hx
  split_ifs at hx ⊢ with hl
  · rw [hx, grigA_smul_ray]
    unfold flipAfterFirstZero
    rw [dif_pos hz]
    funext i
    simp only [prepend, length_rayPrefix, shiftRay]
    by_cases hi : i < k + 1
    · rw [dif_pos hi, getElem_rayPrefix, if_neg (by omega)]
    · rw [dif_neg hi]
      by_cases hi' : i = k + 1
      · subst hi'; simp [k]
      · rw [if_neg (by omega), if_neg hi']; congr 1; omega
  · rw [hx, one_smul_ray, prepend_rayPrefix_shiftRay]

/-- The number of labels `s ∈ (a, b_ω, c_ω, d_ω)` with `y = x·s` does not depend on `ω`: the
values `x·b_ω, x·c_ω, x·d_ω` are `x` once and the flip twice (all three `x` at `1^∞`). -/
theorem card_smul_labels_eq (ω ω' : ℕ → Fin 3) (x y : Ray) :
    Nat.card {i : Fin 4 // y = x <• ![grigA, gen ω .b, gen ω .c, gen ω .d] i} =
      Nat.card {i : Fin 4 // y = x <• ![grigA, gen ω' .b, gen ω' .c, gen ω' .d] i} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  by_cases hz : ∃ k, x k = false
  · simp only [gen_smul_eq_ite ω _ x hz, gen_smul_eq_ite ω' _ x hz]
    generalize ω (Nat.find hz) = l
    generalize ω' (Nat.find hz) = l'
    fin_cases l <;> fin_cases l' <;> simp [letterValue, BCD.killedBy] <;>
      by_cases h1 : y = x <• grigA <;> by_cases h2 : y = flipAfterFirstZero x <;>
      by_cases h3 : y = x <;> simp [h1, h2, h3] <;> omega
  · push Not at hz
    have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
    simp only [hx, oneRay_smul_gen]

end SchreierIndepDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open SchreierIndepDev in
theorem solution (ω ω' : ℕ → Fin 3) :
    orbitOne ω = orbitOne ω' ∧
      (∀ x ∈ orbitOne ω, ∀ y : Ray, (∃ s ∈ gens ω, y = x <• s) ↔ ∃ s ∈ gens ω', y = x <• s) ∧
      (∀ x ∈ orbitOne ω, ∀ y : Ray,
        Nat.card {i : Fin 4 // y = x <• ![Garrido.grigA, gen ω .b, gen ω .c, gen ω .d] i} =
          Nat.card {i : Fin 4 // y = x <• ![Garrido.grigA, gen ω' .b, gen ω' .c, gen ω' .d] i}) ∧
      ∀ x ∈ orbitOne ω, ∀ y ∈ orbitOne ω, schreierDist ω x y = schreierDist ω' x y := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1
  refine ⟨?_, fun x _ y => adjacent_iff ω ω' x y, fun x _ y => card_smul_labels_eq ω ω' x y,
    fun x _ y _ => ?_⟩
  · unfold orbitOne
    rw [(hA2 ω oneRay).1, (hA2 ω' oneRay).1]
  · unfold schreierDist
    congr 1
    ext n
    exact ⟨reach_iff ω ω' x y n, reach_iff ω' ω x y n⟩
end
