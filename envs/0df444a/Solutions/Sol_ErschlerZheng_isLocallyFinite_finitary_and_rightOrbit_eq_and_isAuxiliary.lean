-- Prove2me | solution 1 for ErschlerZheng.isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T00:28:19.596988+00:00
-- url     : https://prove2.me/submissions/f2b28d83-9d0b-4293-aa5b-279f8572277f

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

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

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

theorem rayPrefix_succ (x : Ray) (n : ℕ) :
    rayPrefix x (n + 1) = x 0 :: rayPrefix (shiftRay x 1) n := by
  simp [rayPrefix, List.ofFn_succ, shiftRay]

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

theorem shiftRay_smul_one (g : BinaryTreeAut) (x : Ray) :
    shiftRay (x <• g) 1 = shiftRay x 1 <• sec g [x 0] := by
  rw [shiftRay_smul, singleton_rayPrefix]

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

theorem ray_smul_list_cons (x : Ray) (s : BinaryTreeAut) (l : List BinaryTreeAut) :
    x <• (s :: l).prod = (x <• s) <• l.prod := by
  rw [List.prod_cons, MulOpposite.op_mul, mul_smul]

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

end SchreierDev

end ErschlerZheng
end

section
/-!
# A2: `L` is locally finite; `G_ω`- and `L`-orbits are cofinality classes; `L` is auxiliary (p. 18)

- `G_ω`-orbits: generators change finitely many digits; conversely the Gray-code path at level `N`
  (whose sections at the intermediate words are trivial) carries any common tail along.
- `L`-orbits: finitary elements fix the tail beyond their level; conversely the digit-flip
  automorphism `D_p` (flip the digits where `p` is true) is finitary when `p` is eventually false.
- Local finiteness: a finite subset of `L` lies in the subgroup `K_N` of elements with trivial
  sections at level `N`, which embeds in the maps of level `N` to itself.
- Trivial isotropy: a finitary `h` fixing `x` fixes every `y` with the same first `N` digits.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace OrbitsDev

open GrigBasic RayBasic GrayDev SchreierDev

/-- Eventual agreement of rays. -/
def Cof (x y : Ray) : Prop := ∀ᶠ n in Filter.atTop, y n = x n

theorem cof_refl (x : Ray) : Cof x x := Filter.Eventually.of_forall fun _ => rfl

theorem cof_symm {x y : Ray} (h : Cof x y) : Cof y x := h.mono fun _ h => h.symm

theorem cof_trans {x y z : Ray} (h1 : Cof x y) (h2 : Cof y z) : Cof x z :=
  (h1.and h2).mono fun _ h => h.2.trans h.1

theorem cof_of_shiftRay_eq {x y : Ray} {N : ℕ} (h : shiftRay y N = shiftRay x N) : Cof x y := by
  rw [Cof, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have := congrFun h (n - N)
  simpa [shiftRay, show n - N + N = n by omega] using this

/-! ### `G_ω`-orbits -/

theorem cof_smul_gens (ω : ℕ → Fin 3) {s : BinaryTreeAut} (hs : s ∈ gens ω) (x : Ray) :
    Cof x (x <• s) := by
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · apply cof_of_shiftRay_eq (N := 1)
    rw [shiftRay_smul_one, sec_grigA, one_smul_ray]
  all_goals
    classical
    by_cases hz : ∃ k, x k = false
    · have hk : x (Nat.find hz) = false := Nat.find_spec hz
      have hmin : ∀ j < Nat.find hz, x j = true := fun j hj => by
        have := Nat.find_min hz hj
        simpa using this
      apply cof_of_shiftRay_eq (N := Nat.find hz + 2)
      rw [shiftRay_smul]
      have hpre : rayPrefix x (Nat.find hz + 2) =
          List.replicate (Nat.find hz) true ++ false :: [x (Nat.find hz + 1)] := by
        apply List.ext_getElem
        · simp [length_rayPrefix]
        · intro i h1 h2
          rw [getElem_rayPrefix]
          simp only [length_rayPrefix] at h1
          by_cases hi : i < Nat.find hz
          · rw [List.getElem_append_left (by simpa using hi)]
            simp [hmin i hi]
          · rw [List.getElem_append_right (by simpa using hi)]
            simp only [List.length_replicate]
            rcases (show i = Nat.find hz ∨ i = Nat.find hz + 1 by omega) with e | e
            · subst e; simp [hk]
            · subst e; simp
      rw [hpre, sec_gen_replicate _ _ _ _ (by simp), one_smul_ray]
    · push Not at hz
      have hx : x = oneRay := funext fun k => by simpa [oneRay] using hz k
      rw [hx, oneRay_smul_gen]
      exact cof_refl _

theorem cof_smul_of_mem (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) (x : Ray) :
    Cof x (x <• g) := by
  suffices H : ∀ x, Cof x (x <• g) from H x
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact cof_smul_gens ω hs
  | one => intro x; rw [one_smul_ray]; exact cof_refl x
  | mul g h _ _ ihg ihh =>
    intro x
    rw [MulOpposite.op_mul, mul_smul]
    exact cof_trans (ihg x) (ihh _)
  | inv g _ ihg =>
    intro x
    have := ihg (x <• g⁻¹)
    have e : (x <• g⁻¹) <• g = x := by
      rw [← mul_smul, ← MulOpposite.op_mul, inv_mul_cancel, MulOpposite.op_one, one_smul]
    rw [e] at this
    exact cof_symm this

theorem list_prod_mem (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    l.prod ∈ grigorchuk ω :=
  Subgroup.list_prod_mem _ fun s hs => Subgroup.subset_closure (hl s hs)

theorem exists_mem_smul_eq (ω : ℕ → Fin 3) {x y : Ray} (h : Cof x y) :
    ∃ g ∈ grigorchuk ω, y = x <• g := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have ht : shiftRay y N = shiftRay x N := funext fun i => hN (i + N) (by omega)
  obtain ⟨l, -, hls, hp⟩ := exists_path ω _ (rayPrefix x N) (rayPrefix y N)
    (by simp [length_rayPrefix]) (Int.natCast_natAbs _).symm (shiftRay x N)
  refine ⟨l.prod, list_prod_mem ω l hls, ?_⟩
  rw [prepend_rayPrefix_shiftRay, ← ht, prepend_rayPrefix_shiftRay] at hp
  exact hp.symm

/-! ### The digit-flip automorphisms -/

/-- Flip the digits at the positions where `p` is true. -/
def flipFun : (ℕ → Bool) → List Bool → List Bool
  | _, [] => []
  | p, b :: v => xor (p 0) b :: flipFun (fun i => p (i + 1)) v

theorem flipFun_involutive (p : ℕ → Bool) (v : List Bool) : flipFun p (flipFun p v) = v := by
  induction v generalizing p with
  | nil => rfl
  | cons b v ih => simp [flipFun, ih]

theorem length_flipFun (p : ℕ → Bool) (v : List Bool) : (flipFun p v).length = v.length := by
  induction v generalizing p with
  | nil => rfl
  | cons b v ih => simp [flipFun, ih]

theorem flipFun_append (p : ℕ → Bool) (u v : List Bool) :
    flipFun p (u ++ v) = flipFun p u ++ flipFun (fun i => p (i + u.length)) v := by
  induction u generalizing p with
  | nil => simp [flipFun]
  | cons b u ih =>
    simp only [List.cons_append, flipFun, ih, List.length_cons]
    congr 3

theorem flipFun_prefix (p : ℕ → Bool) (v w : List Bool) (h : v <+: w) :
    flipFun p v <+: flipFun p w := by
  obtain ⟨t, rfl⟩ := h
  rw [flipFun_append]
  exact List.prefix_append _ _

/-- The digit-flip automorphism. -/
def flipAut (p : ℕ → Bool) : BinaryTreeAut :=
  ⟨⟨flipFun p, flipFun p, flipFun_involutive p, flipFun_involutive p⟩,
    length_flipFun p,
    fun v w => ⟨flipFun_prefix p v w, fun h => by
      simpa [flipFun_involutive] using flipFun_prefix p _ _ h⟩⟩

theorem flipAut_mul_self (p : ℕ → Bool) : flipAut p * flipAut p = 1 :=
  Subtype.ext (Equiv.ext fun w => flipFun_involutive p w)

theorem vertex_smul_flipAut (p : ℕ → Bool) (v : List Bool) : v <• flipAut p = flipFun p v := by
  rw [vertex_smul_def, inv_eq_of_mul_eq_one_right (flipAut_mul_self p)]
  rfl

theorem flipFun_rayPrefix (p : ℕ → Bool) (x : Ray) (n : ℕ) :
    flipFun p (rayPrefix x n) = rayPrefix (fun i => xor (p i) (x i)) n := by
  induction n generalizing p x with
  | zero => rfl
  | succ n ih =>
    rw [rayPrefix_succ, rayPrefix_succ, flipFun, ih]
    rfl

theorem ray_smul_flipAut (p : ℕ → Bool) (x : Ray) :
    x <• flipAut p = fun i => xor (p i) (x i) := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, vertex_smul_flipAut, flipFun_rayPrefix]

theorem flipFun_false (v : List Bool) : flipFun (fun _ => false) v = v := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [flipFun, ih]

theorem sec_flipAut (p : ℕ → Bool) (v : List Bool) :
    sec (flipAut p) v = flipAut (fun i => p (i + v.length)) := by
  apply sec_unique
  intro w
  rw [vertex_smul_flipAut, vertex_smul_flipAut, vertex_smul_flipAut, flipFun_append]

theorem flipAut_false : flipAut (fun _ => false) = 1 :=
  Subtype.ext (Equiv.ext fun w => flipFun_false w)

theorem flipAut_mem_finitary (p : ℕ → Bool) (N : ℕ) (hp : ∀ i ≥ N, p i = false) :
    flipAut p ∈ finitary := by
  refine ⟨N, fun v hv => ?_⟩
  rw [sec_flipAut, hv]
  convert flipAut_false using 2
  funext i
  exact hp _ (by omega)

/-! ### `L`-orbits -/

theorem cof_smul_finitary {g : BinaryTreeAut} (hg : g ∈ finitary) (x : Ray) : Cof x (x <• g) := by
  obtain ⟨N, hN⟩ := hg
  apply cof_of_shiftRay_eq (N := N)
  rw [shiftRay_smul, hN _ (length_rayPrefix x N), one_smul_ray]

theorem exists_finitary_smul_eq {x y : Ray} (h : Cof x y) : ∃ g ∈ finitary, y = x <• g := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine ⟨flipAut fun i => xor (x i) (y i), flipAut_mem_finitary _ N fun i hi => ?_, ?_⟩
  · rw [hN i hi]; simp
  · rw [ray_smul_flipAut]
    funext i
    cases x i <;> cases y i <;> rfl

theorem rightOrbit_eq_cof (K : Subgroup BinaryTreeAut) (x : Ray)
    (h1 : ∀ g ∈ K, Cof x (x <• g)) (h2 : ∀ y, Cof x y → ∃ g ∈ K, y = x <• g) :
    rightOrbit K x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n} := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩; exact h1 g hg
  · intro hy; exact h2 y hy

/-! ### Local finiteness -/

/-- `K_N`: trivial sections at every vertex of level `N`. -/
def levelFin (N : ℕ) : Subgroup BinaryTreeAut where
  carrier := {g | ∀ v : List Bool, v.length = N → sec g v = 1}
  mul_mem' := by
    intro g h hg hh v hv
    rw [sec_mul, hg v hv, hh _ (by rw [length_vertex_smul, hv]), one_mul]
  one_mem' := fun v _ => sec_one v
  inv_mem' := by
    intro g hg v hv
    rw [sec_inv, hg _ (by rw [length_vertex_smul, hv]), inv_one]

theorem eq_of_levelFin {N : ℕ} {g h : BinaryTreeAut} (hg : g ∈ levelFin N) (hh : h ∈ levelFin N)
    (heq : ∀ v : List Bool, v.length = N → v <• g = v <• h) : g = h := by
  have key : ∀ w : List Bool, w <• g = w <• h := by
    intro w
    by_cases hw : N ≤ w.length
    · have hsplit : w = w.take N ++ w.drop N := (List.take_append_drop N w).symm
      have hl : (w.take N).length = N := by simp [hw]
      rw [hsplit, append_vertex_smul, append_vertex_smul, hg _ hl, hh _ hl, heq _ hl]
    · set u := w ++ List.replicate (N - w.length) true
      have hl : u.length = N := by simp [u]; omega
      have hpg : w <• g <+: u <• g := (vertex_smul_prefix_iff g w u).2 (List.prefix_append _ _)
      have hph : w <• h <+: u <• h := (vertex_smul_prefix_iff h w u).2 (List.prefix_append _ _)
      rw [heq u hl] at hpg
      exact (List.prefix_of_prefix_length_le hpg hph (by rw [length_vertex_smul,
        length_vertex_smul])).eq_of_length (by rw [length_vertex_smul, length_vertex_smul])
  have : g⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem finite_levelFin (N : ℕ) : (levelFin N : Set BinaryTreeAut).Finite := by
  let f : levelFin N → (List.Vector Bool N → List.Vector Bool N) := fun g v =>
    ⟨v.1 <• (g : BinaryTreeAut), by rw [length_vertex_smul]; exact v.2⟩
  have hf : Function.Injective f := by
    intro g h e
    apply Subtype.ext
    apply eq_of_levelFin g.2 h.2
    intro v hv
    have := congrFun e ⟨v, hv⟩
    exact congrArg Subtype.val this
  have : Finite (levelFin N) := Finite.of_injective f hf
  exact Set.toFinite _

theorem levelFin_mono {N M : ℕ} (h : N ≤ M) : levelFin N ≤ levelFin M :=
  fun g hg => sec_eq_one_of_le g h hg

theorem exists_levelFin (s : Finset BinaryTreeAut) (hs : (s : Set BinaryTreeAut) ⊆ finitary) :
    ∃ N, (s : Set BinaryTreeAut) ⊆ levelFin N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, hN⟩ := ih (fun x hx => hs (by simp [hx]))
    obtain ⟨M, hM⟩ := hs (by simp : a ∈ ((insert a s : Finset BinaryTreeAut) : Set _))
    refine ⟨max N M, ?_⟩
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
    rcases hx with rfl | hx
    · exact levelFin_mono (le_max_right N M) hM
    · exact levelFin_mono (le_max_left N M) (hN hx)

/-! ### Trivial isotropy of `L` -/

theorem eventually_rayPrefix_eq (x : Ray) (n : ℕ) :
    ∀ᶠ y in nhds x, rayPrefix y n = rayPrefix x n := by
  have : ∀ᶠ y in nhds x, ∀ i : Fin n, y i = x i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply (i : ℕ)).continuousAt (x := x)
      ((isOpen_discrete {x i}).mem_nhds rfl)
  filter_upwards [this] with y hy
  simp only [rayPrefix]
  congr 1
  funext i
  exact hy i

theorem germEq_one_of_finitary {h : BinaryTreeAut} (hh : h ∈ finitary) {x : Ray}
    (hx : x <• h = x) : GermEq x h 1 := by
  obtain ⟨N, hN⟩ := hh
  filter_upwards [eventually_rayPrefix_eq x N] with y hy
  rw [one_smul_ray]
  conv_lhs => rw [← prepend_rayPrefix_shiftRay y N]
  rw [prepend_smul, hN _ (length_rayPrefix y N), one_smul_ray, hy, ← rayPrefix_smul, hx, ← hy,
    prepend_rayPrefix_shiftRay]

theorem isotropy_finitary (x : Ray) : isotropy finitary x = ⊥ := by
  unfold isotropy
  rw [Subgroup.map_eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hL, hx⟩ := Subgroup.mem_inf.mp hh
  rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact germEq_one_of_finitary hL hx

end OrbitsDev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open OrbitsDev in
theorem solution :
    (∀ s : Finset Garrido.BinaryTreeAut, (s : Set Garrido.BinaryTreeAut) ⊆ finitary →
      (Subgroup.closure (s : Set Garrido.BinaryTreeAut) : Set Garrido.BinaryTreeAut).Finite) ∧
    (∀ (ω : ℕ → Fin 3) (x : Ray),
      rightOrbit (grigorchuk ω) x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n} ∧
        rightOrbit finitary x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n}) ∧
    ∀ ω : ℕ → Fin 3, IsAuxiliary (X := Ray) (grigorchuk ω) finitary := by
  have horb : ∀ (ω : ℕ → Fin 3) (x : Ray),
      rightOrbit (grigorchuk ω) x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n} ∧
        rightOrbit finitary x = {y : Ray | ∀ᶠ n in Filter.atTop, y n = x n} := fun ω x =>
    ⟨rightOrbit_eq_cof _ x (fun g hg => cof_smul_of_mem ω hg x)
        (fun y hy => exists_mem_smul_eq ω hy),
      rightOrbit_eq_cof _ x (fun g hg => cof_smul_finitary hg x)
        (fun y hy => exists_finitary_smul_eq hy)⟩
  refine ⟨fun s hs => ?_, horb, fun ω => ⟨fun x => ?_, isotropy_finitary⟩⟩
  · obtain ⟨N, hN⟩ := exists_levelFin s hs
    exact (finite_levelFin N).subset ((Subgroup.closure_le _).mpr hN)
  · rw [(horb ω x).1, (horb ω x).2]
end
