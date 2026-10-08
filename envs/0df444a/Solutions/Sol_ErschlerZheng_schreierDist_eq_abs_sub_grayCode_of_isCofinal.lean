-- Prove2me | solution 1 for ErschlerZheng.schreierDist_eq_abs_sub_grayCode_of_isCofinal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:28:45.592816+00:00
-- url     : https://prove2.me/submissions/d8248d31-8f81-4972-9bf4-6ee551a5b775

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

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem sec_grigA (x : Bool) : sec grigA [x] = 1 := by
  apply sec_unique
  intro w
  rw [vertex_smul_grigA, vertex_smul_grigA]
  rfl

theorem sec_grigA_cons (x : Bool) (u : List Bool) : sec grigA (x :: u) = 1 := by
  rw [sec_cons, sec_grigA, sec_one]

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

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

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

theorem grayList_replicate_true (k : ℕ) : grayList (List.replicate k true) = 0 := by
  have := grayList_append_replicate [] k
  simpa [grayList] using this

theorem grayList_replicate_false (k : ℕ) :
    grayList (List.replicate k true ++ [false]) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp [grayList]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, grayList_cons, ih]
    have h1 : (true :: (List.replicate k true ++ [false])).count false = 1 := by
      simp [List.count_append, List.count_replicate]
    rw [h1]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (k + 1)]
    omega

/-- The move of `a`. -/
theorem grayList_grigAFun (w : List Bool) (hw : w ≠ []) :
    (grayList (grigAFun w) : ℤ) = grayList w + (if w.count false % 2 = 0 then 1 else -1) ∧
      (grigAFun w).count false % 2 ≠ w.count false % 2 := by
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [grigAFun, grayList_cons]
  cases b <;> simp [List.count_cons] <;> split_ifs <;> omega

/-- The move of `γ_ω`: identity, or a step of `∓1` that flips the parity of the zeros. -/
theorem grayList_genFun (ω : ℕ → Fin 3) (γ : BCD) (w : List Bool) :
    genFun ω γ w = w ∨
      ((genFun ω γ w).count false % 2 ≠ w.count false % 2 ∧
        (grayList (genFun ω γ w) : ℤ) = grayList w + (if w.count false % 2 = 0 then -1 else 1)) := by
  induction w generalizing ω with
  | nil => left; rfl
  | cons b v ih =>
    cases b
    · by_cases hl : letterValue (ω 0) γ
      · by_cases hv : v = []
        · left; subst hv; simp [genFun, hl, grigAFun]
        · right
          have ha := grayList_grigAFun v hv
          simp only [genFun, hl, if_true, grayList_cons]
          simp only [List.count_cons] at ha ⊢
          simp at ha ⊢
          omega
      · left; simp [genFun, hl]
    · rcases ih (shiftSeq ω 1) with h | ⟨h1, h2⟩
      · left; simp [genFun, h]
      · right
        simp only [genFun, grayList_cons]
        simp only [List.count_cons] at h1 h2 ⊢
        simp at h1 h2 ⊢
        omega

theorem grayList_inj : ∀ (v w : List Bool), v.length = w.length → grayList v = grayList w → v = w
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: v, c :: w, hl, hg => by
    rw [grayList_cons, grayList_cons] at hg
    have h1 : (b :: v).count false % 2 = (c :: w).count false % 2 := by omega
    have h2 : grayList v = grayList w := by omega
    have hv := grayList_inj v w (by simpa using hl) h2
    subst hv
    cases b <;> cases c <;> simp [List.count_cons] at h1 ⊢ <;> omega

theorem exists_first_false (w : List Bool) (hw : false ∈ w) :
    ∃ k z, w = List.replicate k true ++ false :: z := by
  induction w with
  | nil => simp at hw
  | cons b v ih =>
    cases b
    · exact ⟨0, v, rfl⟩
    · obtain ⟨k, z, rfl⟩ := ih (by simpa using hw)
      exact ⟨k + 1, z, rfl⟩

theorem genFun_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) :
    genFun ω γ (List.replicate k true ++ false :: z) =
      List.replicate k true ++ false :: (if letterValue (ω k) γ then grigAFun z else z) := by
  induction k generalizing ω with
  | zero => simp [genFun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, genFun, ih]
    simp only [shiftSeq]
    rfl

theorem sec_gen_cons_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (true :: u) = sec (gen (shiftSeq ω 1) γ) u := by
  rw [sec_cons, sec_gen_true]

theorem sec_gen_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) (hz : z ≠ []) :
    sec (gen ω γ) (List.replicate k true ++ false :: z) = 1 := by
  induction k generalizing ω with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [sec_cons, sec_gen_false]
    obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hz
    unfold letterElt
    split_ifs
    · exact sec_grigA_cons c z'
    · exact sec_one _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sec_gen_cons_true, ih]

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

/-- A step up the Gray code with trivial section. -/
theorem exists_step_up (ω : ℕ → Fin 3) (w : List Bool) (hw : grayList w + 1 < 2 ^ w.length) :
    ∃ s ∈ gens ω, grayList (w <• s) = grayList w + 1 ∧ sec s w = 1 := by
  have hne : w ≠ [] := by rintro rfl; simp [grayList] at hw
  by_cases hz : w.count false % 2 = 0
  · refine ⟨grigA, grigA_mem_gens ω, ?_, ?_⟩
    · have := (grayList_grigAFun w hne).1
      rw [if_pos hz] at this
      rw [vertex_smul_grigA]; omega
    · obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hne
      exact sec_grigA_cons b v
  · have hf : false ∈ w := by
      by_contra h
      rw [List.count_eq_zero.mpr h] at hz
      simp at hz
    obtain ⟨k, z, rfl⟩ := exists_first_false w hf
    have hzne : z ≠ [] := by
      rintro rfl
      rw [grayList_replicate_false] at hw
      simp at hw
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    obtain ⟨γ, hγ⟩ := exists_letterValue (ω k)
    refine ⟨gen ω γ, gen_mem_gens ω γ, ?_, sec_gen_replicate ω γ k z hzne⟩
    rw [vertex_smul_gen]
    rcases grayList_genFun ω γ (List.replicate k true ++ false :: z) with h | ⟨_, h2⟩
    · exfalso
      simp only [genFun_replicate, hγ, ↓reduceIte] at h
      have := List.append_cancel_left h
      simp only [List.cons.injEq, true_and] at this
      obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hzne
      simp [grigAFun] at this
    · rw [if_neg hz] at h2
      omega

/-- A step down the Gray code with trivial section. -/
theorem exists_step_down (ω : ℕ → Fin 3) (w : List Bool) (hw : 0 < grayList w) :
    ∃ s ∈ gens ω, grayList (w <• s) + 1 = grayList w ∧ sec s w = 1 := by
  have hne : w ≠ [] := by rintro rfl; simp [grayList] at hw
  by_cases hz : w.count false % 2 = 1
  · refine ⟨grigA, grigA_mem_gens ω, ?_, ?_⟩
    · have := (grayList_grigAFun w hne).1
      rw [if_neg (by omega)] at this
      rw [vertex_smul_grigA]; omega
    · obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hne
      exact sec_grigA_cons b v
  · have hf : false ∈ w := by
      by_contra h
      have hrep : w = List.replicate w.length true := by
        apply List.eq_replicate_iff.mpr
        refine ⟨rfl, fun b hb => ?_⟩
        cases b
        · exact absurd hb h
        · rfl
      rw [hrep, grayList_replicate_true] at hw
      simp at hw
    obtain ⟨k, z, rfl⟩ := exists_first_false w hf
    have hzne : z ≠ [] := by
      rintro rfl
      apply hz
      simp [List.count_append, List.count_replicate]
    obtain ⟨γ, hγ⟩ := exists_letterValue (ω k)
    refine ⟨gen ω γ, gen_mem_gens ω γ, ?_, sec_gen_replicate ω γ k z hzne⟩
    rw [vertex_smul_gen]
    rcases grayList_genFun ω γ (List.replicate k true ++ false :: z) with h | ⟨_, h2⟩
    · exfalso
      simp only [genFun_replicate, hγ, ↓reduceIte] at h
      have := List.append_cancel_left h
      simp only [List.cons.injEq, true_and] at this
      obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hzne
      simp [grigAFun] at this
    · rw [if_pos (by omega)] at h2
      omega

/-- Every generator moves the Gray code by at most one. -/
theorem grayList_smul_gens (ω : ℕ → Fin 3) (w : List Bool) (s : BinaryTreeAut) (hs : s ∈ gens ω) :
    (grayList (w <• s) : ℤ) - grayList w ∈ ({-1, 0, 1} : Set ℤ) := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [vertex_smul_grigA]
    by_cases hw : w = []
    · subst hw; simp [grigAFun]
    · have := (grayList_grigAFun w hw).1
      split_ifs at this <;> simp [this]
  all_goals
    rw [vertex_smul_gen]
  · rcases grayList_genFun ω .b w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]
  · rcases grayList_genFun ω .c w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]
  · rcases grayList_genFun ω .d w with h | ⟨_, h2⟩
    · simp [h]
    · split_ifs at h2 <;> simp [h2]

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

theorem eq_prepend {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    x = prepend (rayPrefix x N) oneRay := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay x N]
  rw [shiftRay_eq_oneRay h]

theorem allOnesFrom_prepend (w : List Bool) : AllOnesFrom w.length (prepend w oneRay) := by
  intro k hk
  simp [prepend, oneRay, show ¬ k < w.length by omega]

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

theorem genFun_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    genFun ω γ (List.replicate n true) = List.replicate n true := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, genFun, ih]

theorem oneRay_smul_gen (ω : ℕ → Fin 3) (γ : BCD) : oneRay <• gen ω γ = oneRay := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, rayPrefix_oneRay, vertex_smul_gen, genFun_replicate_true]

theorem sec_gen_append_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (u ++ [true]) = 1 ∨
      sec (gen ω γ) (u ++ [true]) = gen (shiftSeq ω (u.length + 1)) γ := by
  induction u generalizing ω with
  | nil =>
    right
    simp only [List.nil_append, sec_gen_true, List.length_nil, zero_add]
  | cons b u ih =>
    cases b
    · left
      rw [List.cons_append, sec_cons, sec_gen_false]
      unfold letterElt
      split_ifs
      · rw [show u ++ [true] = (u ++ [true]).head (by simp) :: (u ++ [true]).tail by simp,
          sec_grigA_cons]
      · exact sec_one _
    · rw [List.cons_append, sec_cons, sec_gen_true]
      rcases ih (shiftSeq ω 1) with h | h
      · left; exact h
      · right; rw [h, shiftSeq_shiftSeq]; simp

theorem oneRay_smul_sec_gens (ω : ℕ → Fin 3) (s : BinaryTreeAut) (hs : s ∈ gens ω)
    (u : List Bool) : oneRay <• sec s (u ++ [true]) = oneRay := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [show u ++ [true] = (u ++ [true]).head (by simp) :: (u ++ [true]).tail by simp,
      sec_grigA_cons]
    exact one_smul _ _
  all_goals
    rcases sec_gen_append_true ω _ u with h | h <;> rw [h]
    · exact one_smul _ _
    · exact oneRay_smul_gen _ _

theorem allOnesFrom_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) {N : ℕ}
    {x : Ray} (h : AllOnesFrom N x) : AllOnesFrom (N + 1) (x <• s) := by
  have h1 := h.mono (Nat.le_succ N)
  have hx := eq_prepend h1
  have hw : rayPrefix x (N + 1) = rayPrefix x N ++ [true] := by
    rw [rayPrefix_add, show rayPrefix (shiftRay x N) 1 = [true] by
      simp [rayPrefix, shiftRay, h N le_rfl]]
  rw [hx, prepend_smul, hw, oneRay_smul_sec_gens ω s hs]
  have := allOnesFrom_prepend ((rayPrefix x N ++ [true]) <• s)
  rwa [length_vertex_smul, List.length_append, length_rayPrefix] at this

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

theorem gray_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) {N : ℕ} {x : Ray}
    (h : AllOnesFrom N x) :
    (grayCode (x <• s) : ℤ) - grayCode x ∈ ({-1, 0, 1} : Set ℤ) := by
  rw [grayCode_eq (allOnesFrom_smul_gens ω hs h), grayCode_eq (h.mono (Nat.le_succ N)),
    rayPrefix_smul]
  exact grayList_smul_gens ω _ s hs

theorem ray_smul_list_cons (x : Ray) (s : BinaryTreeAut) (l : List BinaryTreeAut) :
    x <• (s :: l).prod = (x <• s) <• l.prod := by
  rw [List.prod_cons, MulOpposite.op_mul, mul_smul]

/-- Along a path of generators, the Gray code moves by at most the length. -/
theorem gray_path_le (ω : ℕ → Fin 3) :
    ∀ (l : List BinaryTreeAut), (∀ s ∈ l, s ∈ gens ω) → ∀ (N : ℕ) (x : Ray), AllOnesFrom N x →
      |(grayCode (x <• l.prod) : ℤ) - grayCode x| ≤ l.length ∧
        AllOnesFrom (N + l.length) (x <• l.prod)
  | [], _, N, x, h => by simp [h]
  | s :: l, hl, N, x, h => by
    have hs : s ∈ gens ω := hl s (by simp)
    have h1 := allOnesFrom_smul_gens ω hs h
    obtain ⟨ih1, ih2⟩ := gray_path_le ω l (fun t ht => hl t (by simp [ht])) (N + 1) (x <• s) h1
    have hstep := gray_smul_gens ω hs h
    rw [ray_smul_list_cons]
    refine ⟨?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using ih2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hstep
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [abs_le] at ih1 ⊢
    constructor <;> rcases hstep with e | e | e <;> linarith [ih1.1, ih1.2]

/-- A path of generators between words of the same length, of length the Gray-code distance,
carrying any tail along. -/
theorem exists_path (ω : ℕ → Fin 3) :
    ∀ (m : ℕ) (w w' : List Bool), w.length = w'.length →
      |(grayList w : ℤ) - grayList w'| = m → ∀ t : Ray,
      ∃ l : List BinaryTreeAut, l.length = m ∧ (∀ s ∈ l, s ∈ gens ω) ∧
        prepend w t <• l.prod = prepend w' t
  | 0, w, w', hl, hm, t => by
    have : grayList w = grayList w' := by
      have h0 : (grayList w : ℤ) - grayList w' = 0 := abs_eq_zero.mp (by simpa using hm)
      omega
    rw [grayList_inj w w' hl this]
    exact ⟨[], rfl, by simp, by simp⟩
  | m + 1, w, w', hl, hm, t => by
    have hlt' := grayList_lt w'
    rcases lt_or_gt_of_ne (show grayList w ≠ grayList w' by
      intro e; rw [e, sub_self, abs_zero] at hm; exact absurd hm (by positivity)) with hlt | hgt
    · have hltz : (grayList w : ℤ) < grayList w' := by exact_mod_cast hlt
      have e : (grayList w' : ℤ) - grayList w = m + 1 := by
        rw [abs_of_neg (by linarith)] at hm; push_cast at hm; linarith
      obtain ⟨s, hs, hg, hsec⟩ := exists_step_up ω w (by
        rw [hl]; exact lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hlt')
      have hm' : |(grayList (w <• s) : ℤ) - grayList w'| = m := by
        rw [hg]; push_cast; rw [abs_of_nonpos (by linarith)]; linarith
      obtain ⟨l, hlen, hls, hpath⟩ := exists_path ω m (w <• s) w'
        (by rw [length_vertex_smul, hl]) hm' t
      refine ⟨s :: l, by simp [hlen], ?_, ?_⟩
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hs
        · exact hls u hu
      · rw [ray_smul_list_cons, prepend_smul, hsec, one_smul_ray, hpath]
    · have hgtz : (grayList w' : ℤ) < grayList w := by exact_mod_cast hgt
      have e : (grayList w : ℤ) - grayList w' = m + 1 := by
        rw [abs_of_pos (by linarith)] at hm; push_cast at hm; linarith
      obtain ⟨s, hs, hg, hsec⟩ := exists_step_down ω w (by omega)
      have hg' : (grayList (w <• s) : ℤ) + 1 = grayList w := by exact_mod_cast hg
      have hm' : |(grayList (w <• s) : ℤ) - grayList w'| = m := by
        rw [abs_of_nonneg (by linarith)]; linarith
      obtain ⟨l, hlen, hls, hpath⟩ := exists_path ω m (w <• s) w'
        (by rw [length_vertex_smul, hl]) hm' t
      refine ⟨s :: l, by simp [hlen], ?_, ?_⟩
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hs
        · exact hls u hu
      · rw [ray_smul_list_cons, prepend_smul, hsec, one_smul_ray, hpath]

theorem mem_wordBall_of_list (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    l.prod ∈ Chou.wordBall (gens ω) l.length :=
  ⟨l, le_rfl, fun s hs => Or.inl (hl s hs), rfl⟩

/-- The Schreier distance between two cofinal rays is the Gray-code distance. -/
theorem schreierDist_eq_gray (ω : ℕ → Fin 3) (x y : Ray) (hx : IsCofinal x) (hy : IsCofinal y) :
    (schreierDist ω x y : ℤ) = |(grayCode x : ℤ) - grayCode y| := by
  obtain ⟨N1, h1⟩ := (isCofinal_iff x).mp hx
  obtain ⟨N2, h2⟩ := (isCofinal_iff y).mp hy
  have hx' := h1.mono (le_max_left N1 N2)
  have hy' := h2.mono (le_max_right N1 N2)
  set N := max N1 N2
  set m := ((grayCode x : ℤ) - grayCode y).natAbs with hm
  have hmabs : (m : ℤ) = |(grayCode x : ℤ) - grayCode y| := by
    rw [hm, Int.natCast_natAbs]
  -- the path
  have hpath : ∃ g ∈ Chou.wordBall (gens ω) m, y = x <• g := by
    have := exists_path ω m (rayPrefix x N) (rayPrefix y N) (by simp [length_rayPrefix])
      (by rw [← grayCode_eq hx', ← grayCode_eq hy', hmabs]) oneRay
    obtain ⟨l, hlen, hls, hp⟩ := this
    refine ⟨l.prod, hlen ▸ mem_wordBall_of_list ω l hls, ?_⟩
    rw [← eq_prepend hx', ← eq_prepend hy'] at hp
    exact hp.symm
  have hle : schreierDist ω x y ≤ m := Nat.sInf_le hpath
  have hge : m ≤ schreierDist ω x y := by
    apply le_csInf ⟨m, hpath⟩
    rintro n ⟨g, ⟨l, hlen, hls, rfl⟩, rfl⟩
    have hls' : ∀ s ∈ l, s ∈ gens ω := fun s hs => by
      rcases hls s hs with h | h
      · exact h
      · exact mem_gens_of_inv_mem ω h
    have := (gray_path_le ω l hls' N x hx').1
    rw [abs_sub_comm] at this
    have : (m : ℤ) ≤ n := by rw [hmabs]; linarith [(show (l.length : ℤ) ≤ n by exact_mod_cast hlen)]
    exact_mod_cast this
  rw [← hmabs]
  exact_mod_cast le_antisymm hle hge

end SchreierDev

end ErschlerZheng
end

section
/-!
# A9: `d_𝒮(x, y) = |x̄ - ȳ|` for cofinal rays (p. 34); A9F: the printed prefix sums fail
-/

open scoped RightActions

namespace ErschlerZheng

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
open SchreierDev in
theorem solution (ω : ℕ → Fin 3) (x y : Ray)
    (hx : IsCofinal x) (hy : IsCofinal y) :
    (schreierDist ω x y : ℤ) = |(grayCode x : ℤ) - grayCode y| :=
  schreierDist_eq_gray ω x y hx hy
end
