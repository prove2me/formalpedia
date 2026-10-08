-- Prove2me | solution 1 for ErschlerZheng.isLevelTransitive_and_isotropy_grigorchuk
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:56:19.589514+00:00
-- url     : https://prove2.me/submissions/a8ffc700-8a26-42a9-a85b-eac1c8dad704

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
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

theorem nil_smul (g : BinaryTreeAut) : ([] : List Bool) <• g = [] :=
  List.eq_nil_of_length_eq_zero (length_vertex_smul g [])

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

theorem sec_nil (g : BinaryTreeAut) : sec g [] = g := by
  apply sec_unique
  intro w
  rw [nil_smul]
  rfl

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

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

theorem shiftSeq_zero (ω : ℕ → Fin 3) : shiftSeq ω 0 = ω := by
  funext j; simp [shiftSeq]

/-- The Klein four-group relations: the product of two distinct generators among `b, c, d` is
the third. -/
theorem genFun_klein (ω : ℕ → Fin 3) (w : List Bool) :
    genFun ω .b (genFun ω .c w) = genFun ω .d w ∧
    genFun ω .c (genFun ω .d w) = genFun ω .b w ∧
    genFun ω .d (genFun ω .b w) = genFun ω .c w ∧
    genFun ω .c (genFun ω .b w) = genFun ω .d w ∧
    genFun ω .d (genFun ω .c w) = genFun ω .b w ∧
    genFun ω .b (genFun ω .d w) = genFun ω .c w := by
  induction w generalizing ω with
  | nil => simp [genFun]
  | cons x w ih =>
    cases x
    · have h0 : ω 0 = 0 ∨ ω 0 = 1 ∨ ω 0 = 2 := by
        rcases ω 0 with ⟨k, hk⟩
        interval_cases k <;> simp
      rcases h0 with h0 | h0 | h0 <;>
        simp [genFun, letterValue, BCD.killedBy, h0, grigAFun_involutive w]
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (shiftSeq ω 1)
      simp [genFun, a1, a2, a3, a4, a5, a6]

theorem gen_b_mul_c (ω : ℕ → Fin 3) : gen ω .b * gen ω .c = gen ω .d :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).1)
theorem gen_c_mul_d (ω : ℕ → Fin 3) : gen ω .c * gen ω .d = gen ω .b :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.1)
theorem gen_d_mul_b (ω : ℕ → Fin 3) : gen ω .d * gen ω .b = gen ω .c :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.1)
theorem gen_c_mul_b (ω : ℕ → Fin 3) : gen ω .c * gen ω .b = gen ω .d :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.1)
theorem gen_d_mul_c (ω : ℕ → Fin 3) : gen ω .d * gen ω .c = gen ω .b :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.2.1)
theorem gen_b_mul_d (ω : ℕ → Fin 3) : gen ω .b * gen ω .d = gen ω .c :=
  Subtype.ext (Equiv.ext fun w => (genFun_klein ω w).2.2.2.2.2)

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
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_eq_iff {x : X} {h h' : H} (hh : x <• h = x) (hh' : x <• h' = x) :
    germ x h = germ x h' ↔ GermEq x h h' := by
  rw [germ_def hh, germ_def hh', QuotientGroup.eq]
  change GermEq x (h⁻¹ * h') 1 ↔ GermEq x h h'
  constructor
  · intro e
    have := germEq_comp (germEq_refl x h) (by rw [hh]; exact e)
    rw [mul_inv_cancel_left, mul_one] at this
    exact GermEq.symm' this
  · intro e
    have := germEq_comp (germEq_refl x h⁻¹) (by rw [rsmul_inv_eq hh]; exact e)
    rw [inv_mul_cancel] at this
    exact GermEq.symm' this

theorem germ_mem_isotropy {K : Subgroup H} {x : X} {h : H} (hK : h ∈ K) (hh : x <• h = x) :
    germ x h ∈ isotropy K x := by
  rw [germ_def hh]
  refine ⟨⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.mpr ⟨hK, hh⟩

theorem exists_of_mem_isotropy {K : Subgroup H} {x : X} {γ : GermGroup (H := H) x}
    (hγ : γ ∈ isotropy K x) : ∃ h ∈ K, x <• h = x ∧ germ x h = γ := by
  obtain ⟨a, ha, rfl⟩ := hγ
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
  obtain ⟨hK, hx⟩ := Subgroup.mem_inf.mp ha
  refine ⟨a, hK, hx, ?_⟩
  rw [germ_def hx]
  rfl

end GermBase

end ErschlerZheng
end

section
/-!
# Germs of `G_ω` read from sections along the ray (helpers for B3, B4)

For `k ∈ G_ω ⊔ L` and a ray `x` cofinal with `1^∞`, the sections of `k` along `x` are eventually
the sections along `1^∞` of an element `c ∈ {1, b_ω, c_ω, d_ω}`, i.e. `1` or `γ_{𝔰ⁿω}`; along a ray
not cofinal with `1^∞` they are eventually trivial. Two elements fixing `x` have the same germ at
`x` iff their sections along `x` eventually agree. Orbits and the finitary group come from A2.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ErschlerZheng

namespace GrigGermsDev

open GrigBasic RayBasic GrayDev SchreierDev GermBase

/-! ### Cylinders -/

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

theorem exists_cylinder_subset (x : Ray) {U : Set Ray} (hU : U ∈ nhds x) :
    ∃ n, ∀ y : Ray, rayPrefix y n = rayPrefix x n → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨M, hM⟩ := hI.bddAbove
  refine ⟨M + 1, fun y hy => hsub fun i hi => ?_⟩
  have hiM : i < M + 1 := Nat.lt_succ_of_le (hM hi)
  have : y i = x i := by
    have h1 : i < (rayPrefix y (M + 1)).length := by rw [length_rayPrefix]; exact hiM
    rw [← getElem_rayPrefix y (M + 1) i h1, List.getElem_of_eq hy, getElem_rayPrefix]
  rw [this]
  exact mem_of_mem_nhds (ht i)

theorem cyl_smul (k : BinaryTreeAut) (x y : Ray) (n : ℕ) (hy : rayPrefix y n = rayPrefix x n) :
    y <• k = prepend (rayPrefix x n <• k) (shiftRay y n <• sec k (rayPrefix x n)) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay y n]
  rw [hy, prepend_smul]

theorem germEq_of_sec {x : Ray} {k k' : BinaryTreeAut} {n : ℕ}
    (hv : rayPrefix x n <• k = rayPrefix x n <• k')
    (hs : sec k (rayPrefix x n) = sec k' (rayPrefix x n)) : GermEq x k k' := by
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  rw [cyl_smul k x y n hy, cyl_smul k' x y n hy, hv, hs]

theorem sec_eq_of_vertex_eq {u : List Bool} {k k' : BinaryTreeAut}
    (H : ∀ w : List Bool, (u ++ w) <• k = (u ++ w) <• k') : sec k u = sec k' u := by
  apply sec_unique
  intro w
  rw [H w, append_vertex_smul, ← (show u <• k = u <• k' by simpa using H [])]

theorem sec_eq_of_germEq {x : Ray} {k k' : BinaryTreeAut} (h : GermEq x k k') :
    ∃ N, ∀ n ≥ N, rayPrefix x n <• k = rayPrefix x n <• k' ∧
      sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := exists_cylinder_subset x h
  refine ⟨N, fun n hn => ?_⟩
  have key : ∀ w : List Bool, (rayPrefix x n ++ w) <• k = (rayPrefix x n ++ w) <• k' := by
    intro w
    set y := prepend (rayPrefix x n ++ w) oneRay
    have hyN : rayPrefix y N = rayPrefix x N := by
      have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
        have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
        simpa [length_rayPrefix] using this
      have h2 : rayPrefix y N = (rayPrefix y (n + w.length)).take N := by
        rw [List.prefix_iff_eq_take.mp (rayPrefix_prefix y (show N ≤ n + w.length by omega))]
        simp [length_rayPrefix]
      rw [h2, h1, List.take_append_of_le_length (by rw [length_rayPrefix]; exact hn)]
      have := List.prefix_iff_eq_take.mp (rayPrefix_prefix x hn)
      rw [length_rayPrefix] at this
      exact this.symm
    have hy := hN y hyN
    have := congrArg (fun z => rayPrefix z (n + w.length)) hy
    simp only [rayPrefix_smul] at this
    have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
      have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
      simpa [length_rayPrefix] using this
    rwa [h1] at this
  exact ⟨by simpa using key [], sec_eq_of_vertex_eq key⟩

/-! ### The set `V = {1, b_ω, c_ω, d_ω}` -/

/-- `{1, b_ω, c_ω, d_ω}`. -/
def V (ω : ℕ → Fin 3) : Set BinaryTreeAut := {c | c = 1 ∨ ∃ γ, c = gen ω γ}

theorem one_mem_V (ω : ℕ → Fin 3) : (1 : BinaryTreeAut) ∈ V ω := Or.inl rfl

theorem gen_mem_V (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ V ω := Or.inr ⟨γ, rfl⟩

theorem gen_mul_gen_mem (ω : ℕ → Fin 3) (γ γ' : BCD) : gen ω γ * gen ω γ' ∈ V ω := by
  cases γ <;> cases γ'
  · rw [gen_mul_self]; exact one_mem_V ω
  · rw [gen_b_mul_c]; exact gen_mem_V ω _
  · rw [gen_b_mul_d]; exact gen_mem_V ω _
  · rw [gen_c_mul_b]; exact gen_mem_V ω _
  · rw [gen_mul_self]; exact one_mem_V ω
  · rw [gen_c_mul_d]; exact gen_mem_V ω _
  · rw [gen_d_mul_b]; exact gen_mem_V ω _
  · rw [gen_d_mul_c]; exact gen_mem_V ω _
  · rw [gen_mul_self]; exact one_mem_V ω

theorem V_mul {ω : ℕ → Fin 3} {c c' : BinaryTreeAut} (hc : c ∈ V ω) (hc' : c' ∈ V ω) :
    c * c' ∈ V ω := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · rwa [one_mul]
  · rcases hc' with rfl | ⟨γ', rfl⟩
    · rw [mul_one]; exact gen_mem_V ω γ
    · exact gen_mul_gen_mem ω γ γ'

theorem V_fix {ω : ℕ → Fin 3} {c : BinaryTreeAut} (hc : c ∈ V ω) (n : ℕ) :
    List.replicate n true <• c = List.replicate n true := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · exact one_smul _ _
  · rw [vertex_smul_gen, genFun_replicate_true]

theorem V_oneRay {ω : ℕ → Fin 3} {c : BinaryTreeAut} (hc : c ∈ V ω) : oneRay <• c = oneRay := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · exact one_smul _ _
  · exact oneRay_smul_gen ω γ

theorem sec_V_mul {ω : ℕ → Fin 3} {c c' : BinaryTreeAut} (hc : c ∈ V ω) (n : ℕ) :
    sec (c * c') (List.replicate n true) =
      sec c (List.replicate n true) * sec c' (List.replicate n true) := by
  rw [sec_mul, V_fix hc]

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Cofinality classes are preserved (A2) -/

/-- Eventual agreement of rays. -/
def Cof (x y : Ray) : Prop := ∀ᶠ n in Filter.atTop, y n = x n

theorem cof_symm {x y : Ray} (h : Cof x y) : Cof y x := h.mono fun _ h => h.symm

theorem cof_trans {x y z : Ray} (h1 : Cof x y) (h2 : Cof y z) : Cof x z :=
  (h1.and h2).mono fun _ h => h.2.trans h.1

theorem cof_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary) (x : Ray) :
    Cof x (x <• k) := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 ω
  suffices H : ∀ x, Cof x (x <• k) from H x
  rw [Subgroup.sup_eq_closure] at hk
  induction hk using Subgroup.closure_induction with
  | mem s hs =>
    intro x
    rcases hs with hs | hs
    · have : x <• s ∈ rightOrbit (grigorchuk ω) x := ⟨s, hs, rfl⟩
      rw [(hA2 x).1] at this; exact this
    · have : x <• s ∈ rightOrbit finitary x := ⟨s, hs, rfl⟩
      rw [(hA2 x).2] at this; exact this
  | one => intro x; rw [one_smul_ray]; exact Filter.Eventually.of_forall fun _ => rfl
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

theorem isCofinal_iff_cof (x : Ray) : IsCofinal x ↔ Cof x oneRay :=
  ⟨fun h => h.mono fun _ h => h.symm, fun h => h.mono fun _ h => h.symm⟩

theorem isCofinal_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    {x : Ray} (hx : IsCofinal x) : IsCofinal (x <• k) := by
  rw [isCofinal_iff_cof] at hx ⊢
  exact cof_trans (cof_symm (cof_smul_GL ω hk x)) hx

theorem not_isCofinal_smul_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut}
    (hk : k ∈ grigorchuk ω ⊔ finitary) {x : Ray} (hx : ¬ IsCofinal x) : ¬ IsCofinal (x <• k) := by
  rw [isCofinal_iff_cof] at hx ⊢
  exact fun h => hx (cof_trans (cof_smul_GL ω hk x) h)

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

/-! ### Eventual sections -/

/-- Along a cofinal ray, the sections of `k` are eventually those of some `c ∈ V` along `1^∞`. -/
def ESc (ω : ℕ → Fin 3) (k : BinaryTreeAut) : Prop :=
  ∀ x : Ray, IsCofinal x → ∃ N, ∃ c ∈ V ω, ∀ n ≥ N,
    sec k (rayPrefix x n) = sec c (List.replicate n true)

/-- Along a ray not cofinal with `1^∞`, the sections of `k` are eventually trivial. -/
def ESn (k : BinaryTreeAut) : Prop :=
  ∀ x : Ray, ¬ IsCofinal x → ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = 1

theorem ESc_mul (ω : ℕ → Fin 3) {k k' : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESc ω k) (h2 : ESc ω k') : ESc ω (k * k') := by
  intro x hx
  obtain ⟨N, c, hc, hN⟩ := h1 x hx
  obtain ⟨N', c', hc', hN'⟩ := h2 (x <• k) (isCofinal_smul_GL ω hk hx)
  refine ⟨max N N', c * c', V_mul hc hc', fun n hn => ?_⟩
  rw [sec_mul, ← rayPrefix_smul, hN n (le_of_max_le_left hn), hN' n (le_of_max_le_right hn),
    sec_V_mul hc]

theorem ESc_inv (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESc ω k) : ESc ω k⁻¹ := by
  intro x hx
  obtain ⟨N, c, hc, hN⟩ := h1 (x <• k⁻¹) (isCofinal_smul_GL ω (Subgroup.inv_mem _ hk) hx)
  refine ⟨N, c, hc, fun n hn => ?_⟩
  rw [sec_inv, ← rayPrefix_smul, hN n hn]
  apply inv_eq_of_mul_eq_one_right
  rcases hc with rfl | ⟨γ, rfl⟩
  · rw [sec_one, one_mul]
  · rw [sec_gen_replicate_true, gen_mul_self]

theorem ESn_mul (ω : ℕ → Fin 3) {k k' : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESn k) (h2 : ESn k') : ESn (k * k') := by
  intro x hx
  obtain ⟨N, hN⟩ := h1 x hx
  obtain ⟨N', hN'⟩ := h2 (x <• k) (not_isCofinal_smul_GL ω hk hx)
  refine ⟨max N N', fun n hn => ?_⟩
  rw [sec_mul, ← rayPrefix_smul, hN n (le_of_max_le_left hn), hN' n (le_of_max_le_right hn),
    one_mul]

theorem ESn_inv (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary)
    (h1 : ESn k) : ESn k⁻¹ := by
  intro x hx
  obtain ⟨N, hN⟩ := h1 (x <• k⁻¹) (not_isCofinal_smul_GL ω (Subgroup.inv_mem _ hk) hx)
  refine ⟨N, fun n hn => ?_⟩
  rw [sec_inv, ← rayPrefix_smul, hN n hn, inv_one]

theorem first_zero (x : Ray) (hx : ∃ k, x k = false) :
    ∃ k, x k = false ∧ ∀ j < k, x j = true := by
  classical
  exact ⟨Nat.find hx, Nat.find_spec hx, fun j hj => by simpa using Nat.find_min hx hj⟩

theorem rayPrefix_first_zero' (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true) :
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

theorem rayPrefix_first_zero (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true)
    (n : ℕ) (hn : k + 2 ≤ n) :
    ∃ z : List Bool, z ≠ [] ∧ rayPrefix x n = List.replicate k true ++ false :: z := by
  refine ⟨rayPrefix (shiftRay x (k + 1)) (n - (k + 1)), ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp [length_rayPrefix] at this
    omega
  · rw [show n = (k + 1) + (n - (k + 1)) by omega, rayPrefix_add, rayPrefix_first_zero' x k hk hmin]
    simp [show k + 1 + (n - (k + 1)) - (k + 1) = n - (k + 1) by omega]

theorem ES_gen (ω : ℕ → Fin 3) (γ : BCD) : ESc ω (gen ω γ) ∧ ESn (gen ω γ) := by
  have hzero : ∀ x : Ray, (∃ k, x k = false) → ∃ N, ∀ n ≥ N, sec (gen ω γ) (rayPrefix x n) = 1 := by
    intro x hx
    obtain ⟨k, hk, hmin⟩ := first_zero x hx
    refine ⟨k + 2, fun n hn => ?_⟩
    obtain ⟨z, hz, e⟩ := rayPrefix_first_zero x k hk hmin n hn
    rw [e, sec_gen_replicate ω γ k z hz]
  constructor
  · intro x hx
    by_cases hz : ∃ k, x k = false
    · obtain ⟨N, hN⟩ := hzero x hz
      exact ⟨N, 1, one_mem_V ω, fun n hn => by rw [hN n hn, sec_one]⟩
    · push Not at hz
      have hxo : x = oneRay := funext fun k => by simpa [oneRay] using hz k
      refine ⟨0, gen ω γ, gen_mem_V ω γ, fun n _ => ?_⟩
      rw [hxo, rayPrefix_oneRay]
  · intro x hx
    apply hzero x
    by_contra h
    push Not at h
    apply hx
    exact Filter.Eventually.of_forall fun k => by simpa using h k

theorem ES_grigA (ω : ℕ → Fin 3) : ESc ω grigA ∧ ESn grigA := by
  have h : ∀ x : Ray, ∀ n ≥ 1, sec grigA (rayPrefix x n) = 1 := by
    intro x n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [rayPrefix_succ, sec_grigA_cons]
  exact ⟨fun x _ => ⟨1, 1, one_mem_V ω, fun n hn => by rw [h x n hn, sec_one]⟩,
    fun x _ => ⟨1, h x⟩⟩

theorem ES_finitary (ω : ℕ → Fin 3) {f : BinaryTreeAut} (hf : f ∈ finitary) :
    ESc ω f ∧ ESn f := by
  obtain ⟨m, hm⟩ := hf
  have h : ∀ x : Ray, ∀ n ≥ m, sec f (rayPrefix x n) = 1 := fun x n hn =>
    sec_eq_one_of_le f hn hm _ (length_rayPrefix x n)
  exact ⟨fun x _ => ⟨m, 1, one_mem_V ω, fun n hn => by rw [h x n hn, sec_one]⟩,
    fun x _ => ⟨m, h x⟩⟩

theorem ES_G (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) : ESc ω g ∧ ESn g := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ES_grigA ω
    all_goals exact ES_gen ω _
  | one => exact ES_finitary ω (Subgroup.one_mem _)
  | mul g h hg _ ihg ihh =>
    exact ⟨ESc_mul ω (mem_GL_of_G hg) ihg.1 ihh.1, ESn_mul ω (mem_GL_of_G hg) ihg.2 ihh.2⟩
  | inv g hg ihg =>
    exact ⟨ESc_inv ω (mem_GL_of_G hg) ihg.1, ESn_inv ω (mem_GL_of_G hg) ihg.2⟩

theorem ESc_GL (ω : ℕ → Fin 3) {k : BinaryTreeAut} (hk : k ∈ grigorchuk ω ⊔ finitary) : ESc ω k := by
  have hk' := hk
  rw [Subgroup.sup_eq_closure] at hk'
  induction hk' using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | hs
    · exact (ES_G ω hs).1
    · exact (ES_finitary ω hs).1
  | one => exact (ES_finitary ω (Subgroup.one_mem _)).1
  | mul g h hg _ ihg ihh =>
    rw [← Subgroup.sup_eq_closure] at hg
    exact ESc_mul ω hg (ihg hg) (ihh (by rw [Subgroup.sup_eq_closure]; assumption))
  | inv g hg ihg =>
    rw [← Subgroup.sup_eq_closure] at hg
    exact ESc_inv ω hg (ihg hg)

end GrigGermsDev

end ErschlerZheng
end

section
/-!
# B3: Example 3.2 (p. 18)

Germs of `G_ω` at a ray `x` are read from the sections along `x`: two elements fixing `x` have the
same germ iff their sections along `x` eventually agree (`GrigGermsDev`). Along a ray not cofinal
with `1^∞` the sections are eventually trivial; along a cofinal ray they are eventually `1` or
`γ_{𝔰ⁿω}`. Orbits and level transitivity come from A2 and the Gray-code path.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B3Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev

theorem germ_eq_of_sec' {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    {N : ℕ} (h : ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n)) :
    germ x k = germ x k' := by
  rw [germ_eq_iff hk hk']
  refine germEq_of_sec (n := N) ?_ (h N le_rfl)
  rw [← rayPrefix_smul, ← rayPrefix_smul, hk, hk']

theorem sec_eq_of_germ {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    (h : germ x k = germ x k') : ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := sec_eq_of_germEq ((germ_eq_iff hk hk').mp h)
  exact ⟨N, fun n hn => (hN n hn).2⟩

theorem one_fix (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul_ray x

/-- `ω_j(γ) = id` for every `j` makes `γ_ω` trivial. -/
theorem gen_eq_one_of_forall (ω : ℕ → Fin 3) (γ : BCD) (h : ∀ j, letterValue (ω j) γ = false) :
    gen ω γ = 1 := by
  have key : ∀ (ω : ℕ → Fin 3), (∀ j, letterValue (ω j) γ = false) → ∀ w, genFun ω γ w = w := by
    intro ω h w
    induction w generalizing ω with
    | nil => rfl
    | cons b w ih =>
      cases b
      · simp [genFun, h 0]
      · simp only [genFun]
        rw [ih (shiftSeq ω 1) (fun j => h (j + 1))]
  exact Subtype.ext (Equiv.ext fun w => key ω h w)

theorem gen_eq_of_forall (ω : ℕ → Fin 3) (γ γ' : BCD)
    (h : ∀ j, letterValue (ω j) γ = letterValue (ω j) γ') : gen ω γ = gen ω γ' := by
  have key : ∀ (ω : ℕ → Fin 3), (∀ j, letterValue (ω j) γ = letterValue (ω j) γ') →
      ∀ w, genFun ω γ w = genFun ω γ' w := by
    intro ω h w
    induction w generalizing ω with
    | nil => rfl
    | cons b w ih =>
      cases b
      · simp [genFun, h 0]
      · simp only [genFun]
        rw [ih (shiftSeq ω 1) (fun j => h (j + 1))]
  exact Subtype.ext (Equiv.ext fun w => key ω h w)

theorem gen_ne_one_of_exists (ω : ℕ → Fin 3) (γ : BCD) (h : ∃ j, letterValue (ω j) γ = true) :
    gen ω γ ≠ 1 := by
  obtain ⟨j, hj⟩ := h
  intro e
  have := congrArg (fun g => (List.replicate j true ++ [false, false]) <• g) e
  rw [vertex_smul_gen, show List.replicate j true ++ [false, false] =
    List.replicate j true ++ false :: [false] from rfl, genFun_replicate, hj] at this
  simp only [↓reduceIte, one_smul_ray] at this
  rw [show (List.replicate j true ++ [false, false]) <• (1 : BinaryTreeAut) =
    List.replicate j true ++ [false, false] from one_smul _ _] at this
  have := List.append_cancel_left this
  simp [grigAFun] at this

theorem letterValue_killedBy (i : Fin 3) : letterValue i (BCD.killedBy i) = false := by
  simp [letterValue]

theorem letterValue_of_ne (i : Fin 3) (γ : BCD) (h : γ ≠ BCD.killedBy i) : letterValue i γ = true := by
  simp [letterValue, h]

theorem eq_of_letterValue_false (i : Fin 3) (γ : BCD) (h : letterValue i γ = false) :
    γ = BCD.killedBy i := by
  simpa [letterValue] using h

theorem killedBy_inj {i j : Fin 3} (h : BCD.killedBy i = BCD.killedBy j) : i = j := by
  rcases ZetaFin.fin3 i with rfl | rfl | rfl <;> rcases ZetaFin.fin3 j with rfl | rfl | rfl <;>
    first | rfl | exact absurd h (by decide)
where
  ZetaFin.fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
    rcases i with ⟨k, hk⟩; interval_cases k <;> simp

/-- Not eventually constant: every letter is non-trivial on every tail. -/
theorem gen_shift_ne_one (ω : ℕ → Fin 3) (hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i)
    (γ : BCD) (n : ℕ) : gen (shiftSeq ω n) γ ≠ 1 := by
  apply gen_ne_one_of_exists
  by_contra hcon
  push Not at hcon
  -- every letter from `n` on kills `γ`
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, BCD.killedBy i = γ := by
    cases γ
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  apply hω
  refine ⟨i, Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩⟩
  have := hcon (k - n)
  simp only [shiftSeq, show k - n + n = k by omega, Bool.not_eq_true] at this
  have e := eq_of_letterValue_false _ _ this
  rw [← hi] at e
  exact (killedBy_inj e).symm

theorem gen_shift_inj (ω : ℕ → Fin 3) (hω : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i)
    {γ γ' : BCD} (n : ℕ) (h : gen (shiftSeq ω n) γ = gen (shiftSeq ω n) γ') : γ = γ' := by
  by_contra hne
  have hmul : gen (shiftSeq ω n) γ * gen (shiftSeq ω n) γ' = 1 := by rw [h, gen_mul_self]
  cases γ <;> cases γ' <;> simp at hne
  · rw [gen_b_mul_c] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_b_mul_d] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_c_mul_b] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_c_mul_d] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_d_mul_b] at hmul; exact gen_shift_ne_one ω hω _ n hmul
  · rw [gen_d_mul_c] at hmul; exact gen_shift_ne_one ω hω _ n hmul

theorem V_subset_G (ω : ℕ → Fin 3) {c : BinaryTreeAut} (hc : c ∈ V ω) : c ∈ grigorchuk ω := by
  rcases hc with rfl | ⟨γ, rfl⟩
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (gen_mem_gens ω γ)

/-- An element of `G_ω` mapping `1^∞` to a cofinal `x` with eventually trivial sections along `1^∞`. -/
theorem exists_transport (ω : ℕ → Fin 3) {x : Ray} (hx : IsCofinal x) :
    ∃ h ∈ grigorchuk ω, oneRay <• h = x ∧ ∃ N, ∀ n ≥ N, sec h (List.replicate n true) = 1 := by
  have hA2 := (isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary.2.1 ω oneRay).1
  have hxo : x ∈ rightOrbit (grigorchuk ω) oneRay := by
    rw [hA2]; exact hx
  obtain ⟨h₀, hh₀, rfl⟩ := hxo
  obtain ⟨N, c, hc, hN⟩ := (ES_G ω hh₀).1 oneRay (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨c * h₀, Subgroup.mul_mem _ (V_subset_G ω hc) hh₀, ?_, N, fun n hn => ?_⟩
  · rw [MulOpposite.op_mul, mul_smul]
    show (oneRay <• c) <• h₀ = oneRay <• h₀
    rw [V_oneRay hc]
  · rw [sec_V_mul hc, ← rayPrefix_oneRay, hN n hn, rayPrefix_oneRay]
    rcases hc with rfl | ⟨γ, rfl⟩
    · rw [sec_one, one_mul]
    · rw [sec_gen_replicate_true, gen_mul_self]

theorem allOnes_of_cofinal {x : Ray} (hx : IsCofinal x) : ∃ M, ∀ n ≥ M, shiftRay x n = oneRay := by
  obtain ⟨M, hM⟩ := (isCofinal_iff x).mp hx
  exact ⟨M, fun n hn => shiftRay_eq_oneRay (hM.mono hn)⟩

theorem rayPrefix_of_shift {x : Ray} {n₀ : ℕ} (h : shiftRay x n₀ = oneRay) (n : ℕ) (hn : n₀ ≤ n) :
    rayPrefix x n = rayPrefix x n₀ ++ List.replicate (n - n₀) true := by
  rw [show n = n₀ + (n - n₀) by omega, rayPrefix_add, h, rayPrefix_oneRay]
  simp

/-- The conjugate `h⁻¹ γ h` has sections `γ_{𝔰ⁿω}` along `x`. -/
theorem sec_conj (ω : ℕ → Fin 3) {h : BinaryTreeAut} {x : Ray} (hhx : oneRay <• h = x) {N : ℕ}
    (hN : ∀ n ≥ N, sec h (List.replicate n true) = 1) (γ : BCD) :
    x <• (h⁻¹ * gen ω γ * h) = x ∧
      ∀ n ≥ N, sec (h⁻¹ * gen ω γ * h) (rayPrefix x n) = gen (shiftSeq ω n) γ := by
  have hxh : x <• h⁻¹ = oneRay := by rw [← hhx]; exact rsmul_inv_smul oneRay h
  refine ⟨?_, fun n hn => ?_⟩
  · rw [rsmul_mul, rsmul_mul, hxh, oneRay_smul_gen, hhx]
  · have hp : rayPrefix x n <• h⁻¹ = List.replicate n true := by
      rw [← rayPrefix_smul, hxh, rayPrefix_oneRay]
    rw [sec_mul, sec_mul, sec_inv, hp, vertex_smul_mul, hp, vertex_smul_gen,
      genFun_replicate_true, hN n hn, inv_one, one_mul, mul_one, sec_gen_replicate_true]

/-- Sections along `x` propagate along `1^∞`. -/
theorem sec_along (ω : ℕ → Fin 3) {g : BinaryTreeAut} {x : Ray} {n₀ : ℕ} {γ : BCD}
    (hx : shiftRay x n₀ = oneRay) (hg : sec g (rayPrefix x n₀) = gen (shiftSeq ω n₀) γ) :
    ∀ n ≥ n₀, sec g (rayPrefix x n) = gen (shiftSeq ω n) γ := by
  intro n hn
  rw [rayPrefix_of_shift hx n hn, sec_append, hg, sec_gen_replicate_true, shiftSeq_shiftSeq,
    show n - n₀ + n₀ = n by omega]

theorem germ_eq_one_iff {x : Ray} {k : BinaryTreeAut} (hk : x <• k = x) :
    germ x k = 1 ↔ ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = 1 := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := sec_eq_of_germ hk (one_fix x) (h.trans (germ_one x).symm)
    exact ⟨N, fun n hn => (hN n hn).trans (sec_one _)⟩
  · rintro ⟨N, hN⟩
    rw [← germ_one x]
    exact germ_eq_of_sec' hk (one_fix x) (fun n hn => (hN n hn).trans (sec_one _).symm)

end B3Dev

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open B3Dev GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev in
theorem solution (ω : ℕ → Fin 3) :
    (∀ u v : List Bool, u.length = v.length → ∃ g ∈ grigorchuk ω, u <• g = v) ∧
    (∀ x : Ray, ¬ IsCofinal x → isotropy (grigorchuk ω) x = ⊥) ∧
    (∀ i : Fin 3, (∀ᶠ k in Filter.atTop, ω k = i) →
      germ oneRay (gen ω (BCD.killedBy i)) = 1 ∧
        (∀ γ γ' : BCD, γ ≠ BCD.killedBy i → γ' ≠ BCD.killedBy i →
          germ oneRay (gen ω γ) = germ oneRay (gen ω γ')) ∧
        ∀ x : Ray, IsCofinal x → Nonempty (isotropy (grigorchuk ω) x ≃* Multiplicative (ZMod 2))) ∧
    ((¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, ω k = i) →
      (∀ x : Ray, IsCofinal x →
        isotropy (grigorchuk ω ⊔ finitary) x = isotropy (grigorchuk ω) x ∧
          (∀ g ∈ grigorchuk ω, x <• g = x → germ x g = 1 ∨ ∃ γ : BCD, HasGermAt ω γ g x) ∧
          (∀ γ : BCD, ∃ g ∈ grigorchuk ω, x <• g = x ∧ HasGermAt ω γ g x) ∧
          (∀ (γ : BCD) (g : Garrido.BinaryTreeAut), g ∈ grigorchuk ω → x <• g = x →
            HasGermAt ω γ g x → germ x g ≠ 1) ∧
          (∀ (γ γ' : BCD) (g g' : Garrido.BinaryTreeAut), g ∈ grigorchuk ω → g' ∈ grigorchuk ω →
            x <• g = x → x <• g' = x → HasGermAt ω γ g x → HasGermAt ω γ' g' x →
              (germ x g = germ x g' ↔ γ = γ')) ∧
          Nonempty (isotropy (grigorchuk ω) x ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
      (isotropy (grigorchuk ω) oneRay : Set (GermGroup (H := Garrido.BinaryTreeAut) oneRay)) =
        {germ oneRay (1 : Garrido.BinaryTreeAut), germ oneRay (gen ω .b), germ oneRay (gen ω .c),
          germ oneRay (gen ω .d)} ∧
      germLetterSubgroup ω .b < isotropy (grigorchuk ω ⊔ finitary) oneRay) := by
  have hoc : IsCofinal oneRay := Filter.Eventually.of_forall fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) level transitivity
  · intro u v huv
    obtain ⟨l, -, hls, hp⟩ := exists_path ω _ u v huv (Int.natCast_natAbs _).symm oneRay
    refine ⟨l.prod, Subgroup.list_prod_mem _ fun s hs => Subgroup.subset_closure (hls s hs), ?_⟩
    have := congrArg (fun z => rayPrefix z u.length) hp
    simp only [rayPrefix_smul, rayPrefix_prepend] at this
    rw [this, huv, rayPrefix_prepend]
  -- (2) trivial isotropy off the orbit
  · intro x hx
    unfold isotropy
    rw [Subgroup.map_eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    obtain ⟨hG, hfix⟩ := Subgroup.mem_inf.mp hh
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change GermEq x (h : BinaryTreeAut) 1
    obtain ⟨N, hN⟩ := (ES_G ω hG).2 x hx
    rw [← germ_eq_iff hfix (one_fix x)]
    exact germ_eq_of_sec' hfix (one_fix x) (fun n hn => (hN n hn).trans (sec_one _).symm)
  -- (3) eventually constant
  · intro i hi
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hi
    have hkill : ∀ n ≥ K, gen (shiftSeq ω n) (BCD.killedBy i) = 1 := fun n hn =>
      gen_eq_one_of_forall _ _ fun j => by
        simp only [shiftSeq]; rw [hK (j + n) (by omega)]; exact letterValue_killedBy i
    have hsame : ∀ γ γ' : BCD, γ ≠ BCD.killedBy i → γ' ≠ BCD.killedBy i →
        ∀ n ≥ K, gen (shiftSeq ω n) γ = gen (shiftSeq ω n) γ' := fun γ γ' h1 h2 n hn =>
      gen_eq_of_forall _ _ _ fun j => by
        simp only [shiftSeq]; rw [hK (j + n) (by omega), letterValue_of_ne i γ h1,
          letterValue_of_ne i γ' h2]
    have hne1 : ∀ γ : BCD, γ ≠ BCD.killedBy i → ∀ n ≥ K, gen (shiftSeq ω n) γ ≠ 1 :=
      fun γ h1 n hn => gen_ne_one_of_exists _ _ ⟨0, by
        simp only [shiftSeq, zero_add]; rw [hK n hn]; exact letterValue_of_ne i γ h1⟩
    have hsec_o : ∀ γ : BCD, ∀ n, sec (gen ω γ) (rayPrefix oneRay n) = gen (shiftSeq ω n) γ :=
      fun γ n => by rw [rayPrefix_oneRay, sec_gen_replicate_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [germ_eq_one_iff (oneRay_smul_gen ω _)]
      exact ⟨K, fun n hn => by rw [hsec_o, hkill n hn]⟩
    · intro γ γ' h1 h2
      exact germ_eq_of_sec' (oneRay_smul_gen ω _) (oneRay_smul_gen ω _) (N := K)
        (fun n hn => by rw [hsec_o, hsec_o, hsame γ γ' h1 h2 n hn])
    · intro x hx
      -- a non-killed letter
      obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : BCD, γ₀ ≠ BCD.killedBy i := by
        by_cases h : BCD.killedBy i = .b
        · exact ⟨.c, by rw [h]; decide⟩
        · exact ⟨.b, fun e => h e.symm⟩
      obtain ⟨h, hhG, hhx, Nh, hNh⟩ := exists_transport ω hx
      obtain ⟨hfix0, hsec0⟩ := sec_conj ω hhx hNh γ₀
      set g₀ := h⁻¹ * gen ω γ₀ * h
      have hg₀G : g₀ ∈ grigorchuk ω :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhG)
          (Subgroup.subset_closure (gen_mem_gens ω γ₀))) hhG
      set Θ := germ x g₀
      have hΘ1 : Θ ≠ 1 := by
        intro e
        obtain ⟨N, hN⟩ := (germ_eq_one_iff hfix0).mp e
        exact hne1 γ₀ hγ₀ (max N (max K Nh)) (by omega)
          ((hsec0 _ (by omega)).symm.trans (hN _ (by omega)))
      have hset : (isotropy (grigorchuk ω) x : Set (GermGroup (H := BinaryTreeAut) x)) = {1, Θ} := by
        ext θ
        simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hθ
          obtain ⟨k, hkG, hkx, rfl⟩ := exists_of_mem_isotropy hθ
          obtain ⟨N, c, hc, hN⟩ := (ES_G ω hkG).1 x hx
          rcases hc with rfl | ⟨γ, rfl⟩
          · left
            rw [germ_eq_one_iff hkx]
            exact ⟨N, fun n hn => by rw [hN n hn, sec_one]⟩
          · by_cases hγ : γ = BCD.killedBy i
            · left
              rw [germ_eq_one_iff hkx]
              exact ⟨max N K, fun n hn => by
                rw [hN n (by omega), sec_gen_replicate_true, hγ, hkill n (by omega)]⟩
            · right
              exact germ_eq_of_sec' hkx hfix0 (N := max N (max K Nh)) fun n hn => by
                rw [hN n (by omega), sec_gen_replicate_true, hsec0 n (by omega),
                  hsame γ γ₀ hγ hγ₀ n (by omega)]
        · rintro (rfl | rfl)
          · exact Subgroup.one_mem _
          · exact germ_mem_isotropy hg₀G hfix0
      have hcard : Nat.card (isotropy (grigorchuk ω) x) = 2 := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_pair (Ne.symm hΘ1)]
      exact ⟨mulEquivOfPrimeCardEq hcard (by rw [Nat.card_eq_fintype_card]; rfl)⟩
  -- (4) not eventually constant
  · intro hω
    -- elements with prescribed sections along a cofinal ray
    have conj_data : ∀ x : Ray, IsCofinal x → ∀ γ : BCD, ∃ g ∈ grigorchuk ω, x <• g = x ∧
        ∃ N, ∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) γ := by
      intro x hx γ
      obtain ⟨h, hhG, hhx, Nh, hNh⟩ := exists_transport ω hx
      obtain ⟨hfix0, hsec0⟩ := sec_conj ω hhx hNh γ
      exact ⟨h⁻¹ * gen ω γ * h, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhG)
        (Subgroup.subset_closure (gen_mem_gens ω γ))) hhG, hfix0, Nh, hsec0⟩
    -- HasGermAt gives eventual sections
    have hga : ∀ (x : Ray) (γ : BCD) (g : BinaryTreeAut), HasGermAt ω γ g x →
        ∃ N, ∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) γ := by
      rintro x γ g ⟨n₀, hx0, hg0⟩
      exact ⟨n₀, sec_along ω hx0 hg0⟩
    have hgerm_ne : ∀ (x : Ray) (γ : BCD) (g : BinaryTreeAut), x <• g = x → HasGermAt ω γ g x →
        germ x g ≠ 1 := by
      intro x γ g hgx hg e
      obtain ⟨N, hN⟩ := hga x γ g hg
      obtain ⟨N', hN'⟩ := (germ_eq_one_iff hgx).mp e
      exact gen_shift_ne_one ω hω γ (max N N')
        ((hN _ (le_max_left _ _)).symm.trans (hN' _ (le_max_right _ _)))
    have hgerm_eq : ∀ (x : Ray) (γ γ' : BCD) (g g' : BinaryTreeAut), x <• g = x → x <• g' = x →
        HasGermAt ω γ g x → HasGermAt ω γ' g' x → (germ x g = germ x g' ↔ γ = γ') := by
      intro x γ γ' g g' hgx hg'x hg hg'
      obtain ⟨N, hN⟩ := hga x γ g hg
      obtain ⟨N', hN'⟩ := hga x γ' g' hg'
      constructor
      · intro e
        obtain ⟨M, hM⟩ := sec_eq_of_germ hgx hg'x e
        apply gen_shift_inj ω hω (max M (max N N'))
        rw [← hN _ (by omega), ← hN' _ (by omega)]
        exact hM _ (by omega)
      · rintro rfl
        exact germ_eq_of_sec' hgx hg'x (N := max N N') fun n hn => by
          rw [hN n (by omega), hN' n (by omega)]
    refine ⟨fun x hx => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    -- (a) Ĝ_x = 𝒢_x
    · apply le_antisymm
      · intro θ hθ
        obtain ⟨k, hkGL, hkx, rfl⟩ := exists_of_mem_isotropy hθ
        obtain ⟨N, c, hc, hN⟩ := ESc_GL ω hkGL x hx
        rcases hc with rfl | ⟨γ, rfl⟩
        · have : germ x k = 1 := by
            rw [germ_eq_one_iff hkx]; exact ⟨N, fun n hn => by rw [hN n hn, sec_one]⟩
          rw [this]; exact Subgroup.one_mem _
        · obtain ⟨g, hgG, hgx, N', hN'⟩ := conj_data x hx γ
          have : germ x k = germ x g := germ_eq_of_sec' hkx hgx (N := max N N') fun n hn => by
            rw [hN n (by omega), sec_gen_replicate_true, hN' n (by omega)]
          rw [this]; exact germ_mem_isotropy hgG hgx
      · intro θ hθ
        obtain ⟨k, hkG, hkx, rfl⟩ := exists_of_mem_isotropy hθ
        exact germ_mem_isotropy (mem_GL_of_G hkG) hkx
    -- (b) every germ is trivial or a γ-germ
    · intro g hg hgx
      obtain ⟨N, c, hc, hN⟩ := (ES_G ω hg).1 x hx
      rcases hc with rfl | ⟨γ, rfl⟩
      · left
        rw [germ_eq_one_iff hgx]; exact ⟨N, fun n hn => by rw [hN n hn, sec_one]⟩
      · right
        obtain ⟨M, hM⟩ := allOnes_of_cofinal hx
        refine ⟨γ, max N M, hM _ (le_max_right _ _), ?_⟩
        rw [hN _ (le_max_left _ _), sec_gen_replicate_true]
    -- (c) each γ occurs
    · intro γ
      obtain ⟨g, hgG, hgx, N, hN⟩ := conj_data x hx γ
      obtain ⟨M, hM⟩ := allOnes_of_cofinal hx
      exact ⟨g, hgG, hgx, max N M, hM _ (le_max_right _ _), hN _ (le_max_left _ _)⟩
    -- (d) γ-germs are non-trivial
    · intro γ g _ hgx hg
      exact hgerm_ne x γ g hgx hg
    -- (e) γ-germs are distinct
    · intro γ γ' g g' _ _ hgx hg'x hg hg'
      exact hgerm_eq x γ γ' g g' hgx hg'x hg hg'
    -- (e') 𝒢_x ≅ ℤ/2 × ℤ/2: four elements, each of order at most two
    · have hlab : ∀ γ : BCD, ∃ g ∈ grigorchuk ω, x <• g = x ∧ HasGermAt ω γ g x := fun γ => by
        obtain ⟨g, hgG, hgx, N, hN⟩ := conj_data x hx γ
        obtain ⟨M, hM⟩ := allOnes_of_cofinal hx
        exact ⟨g, hgG, hgx, max N M, hM _ (le_max_right _ _), hN _ (le_max_left _ _)⟩
      choose g hgG hgx hgl using hlab
      have hne1 : ∀ γ, germ x (g γ) ≠ 1 := fun γ => hgerm_ne x γ (g γ) (hgx γ) (hgl γ)
      have hneq : ∀ γ γ', γ ≠ γ' → germ x (g γ) ≠ germ x (g γ') := fun γ γ' h e =>
        h ((hgerm_eq x γ γ' (g γ) (g γ') (hgx γ) (hgx γ') (hgl γ) (hgl γ')).mp e)
      have hset : (isotropy (grigorchuk ω) x : Set (GermGroup (H := BinaryTreeAut) x)) =
          {1, germ x (g .b), germ x (g .c), germ x (g .d)} := by
        ext θ
        simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hθ
          obtain ⟨k, hkG, hkx, rfl⟩ := exists_of_mem_isotropy hθ
          obtain ⟨N, c, hc, hN⟩ := (ES_G ω hkG).1 x hx
          rcases hc with rfl | ⟨γ, rfl⟩
          · left
            rw [germ_eq_one_iff hkx]
            exact ⟨N, fun n hn => by rw [hN n hn, sec_one]⟩
          · right
            obtain ⟨M, hM⟩ := allOnes_of_cofinal hx
            have hkγ : HasGermAt ω γ k x := ⟨max N M, hM _ (le_max_right _ _), by
              rw [hN _ (le_max_left _ _), sec_gen_replicate_true]⟩
            rw [(hgerm_eq x γ γ k (g γ) hkx (hgx γ) hkγ (hgl γ)).mpr rfl]
            rcases γ with _ | _ | _
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl | rfl)
          · exact Subgroup.one_mem _
          all_goals exact germ_mem_isotropy (hgG _) (hgx _)
      have h1 : (1 : GermGroup (H := BinaryTreeAut) x) ∉
          ({germ x (g .b), germ x (g .c), germ x (g .d)} : Set _) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨(hne1 .b).symm, (hne1 .c).symm, (hne1 .d).symm⟩
      have h2 : germ x (g .b) ∉ ({germ x (g .c), germ x (g .d)} : Set _) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hneq .b .c (by decide), hneq .b .d (by decide)⟩
      have hcard : Nat.card (isotropy (grigorchuk ω) x) = 4 := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h1,
          Set.ncard_insert_of_notMem h2, Set.ncard_pair (hneq .c .d (by decide))]
      have hsq : ∀ θ ∈ isotropy (grigorchuk ω) x, θ * θ = 1 := by
        intro θ hθ
        obtain ⟨k, hkG, hkx, rfl⟩ := exists_of_mem_isotropy hθ
        have hkkx : x <• (k * k) = x := by rw [rsmul_mul, hkx, hkx]
        rw [← germ_mul hkx hkx, germ_eq_one_iff hkkx]
        obtain ⟨N, c, hc, hN⟩ := (ES_G ω hkG).1 x hx
        refine ⟨N, fun n hn => ?_⟩
        have hp : rayPrefix x n <• k = rayPrefix x n := by rw [← rayPrefix_smul, hkx]
        rw [sec_mul, hp, hN n hn]
        rcases hc with rfl | ⟨γ, rfl⟩
        · rw [sec_one, mul_one]
        · rw [sec_gen_replicate_true, gen_mul_self]
      have : Nontrivial (isotropy (grigorchuk ω) x) :=
        ⟨⟨⟨_, germ_mem_isotropy (hgG .b) (hgx .b)⟩, 1, fun h => hne1 .b (congrArg Subtype.val h)⟩⟩
      have : IsKleinFour (isotropy (grigorchuk ω) x) :=
        { card_four := hcard
          exponent_two := (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun y hy =>
            orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hsq _ y.2)) hy }
      exact IsKleinFour.nonempty_mulEquiv
    -- (f) 𝒢_o = {id, b, c, d}
    · have hga0 : ∀ γ : BCD, HasGermAt ω γ (gen ω γ) oneRay := fun γ =>
        ⟨0, rfl, by rw [show rayPrefix oneRay 0 = [] from rfl, sec_nil, shiftSeq_zero]⟩
      have hgmem : ∀ γ : BCD, germ oneRay (gen ω γ) ∈ isotropy (grigorchuk ω) oneRay := fun γ =>
        germ_mem_isotropy (Subgroup.subset_closure (gen_mem_gens ω γ)) (oneRay_smul_gen ω γ)
      ext θ
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hθ
        obtain ⟨k, hkG, hkx, rfl⟩ := exists_of_mem_isotropy hθ
        obtain ⟨N, c, hc, hN⟩ := (ES_G ω hkG).1 oneRay hoc
        rcases hc with rfl | ⟨γ, rfl⟩
        · left
          rw [germ_one, germ_eq_one_iff hkx]
          exact ⟨N, fun n hn => by rw [hN n hn, sec_one]⟩
        · right
          obtain ⟨M, hM⟩ := allOnes_of_cofinal hoc
          have hkγ : HasGermAt ω γ k oneRay := ⟨max N M, hM _ (le_max_right _ _), by
            rw [hN _ (le_max_left _ _), sec_gen_replicate_true]⟩
          rw [(hgerm_eq oneRay γ γ k (gen ω γ) hkx (oneRay_smul_gen ω γ) hkγ (hga0 γ)).mpr rfl]
          rcases γ with _ | _ | _
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl | rfl)
        · rw [germ_one]; exact Subgroup.one_mem _
        · exact hgmem .b
        · exact hgmem .c
        · exact hgmem .d
    -- (g) ⟨b⟩ < Ĝ_o
    · have hbo := oneRay_smul_gen ω .b
      have hco := oneRay_smul_gen ω .c
      have hb_ga : HasGermAt ω .b (gen ω .b) oneRay :=
        ⟨0, rfl, by rw [show rayPrefix oneRay 0 = [] from rfl, sec_nil, shiftSeq_zero]⟩
      have hc_ga : HasGermAt ω .c (gen ω .c) oneRay :=
        ⟨0, rfl, by rw [show rayPrefix oneRay 0 = [] from rfl, sec_nil, shiftSeq_zero]⟩
      have hbmem : germ oneRay (gen ω .b) ∈ isotropy (grigorchuk ω ⊔ finitary) oneRay :=
        germ_mem_isotropy (mem_GL_of_G (Subgroup.subset_closure (gen_mem_gens ω .b))) hbo
      have hcmem : germ oneRay (gen ω .c) ∈ isotropy (grigorchuk ω ⊔ finitary) oneRay :=
        germ_mem_isotropy (mem_GL_of_G (Subgroup.subset_closure (gen_mem_gens ω .c))) hco
      have hsq : germ oneRay (gen ω .b) ^ (2 : ℤ) = 1 := by
        rw [zpow_two, ← germ_mul hbo hbo, gen_mul_self, germ_one]
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hbmem) fun e => ?_
      rw [← e] at hcmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcmem
      rw [zpow_eq_zpow_emod k hsq] at hk
      rcases Int.emod_two_eq k with h0 | h1
      · rw [h0, zpow_zero] at hk
        exact hgerm_ne oneRay .c (gen ω .c) hco hc_ga hk.symm
      · rw [h1, zpow_one] at hk
        have := (hgerm_eq oneRay .b .c (gen ω .b) (gen ω .c) hbo hco hb_ga hc_ga).mp hk
        exact absurd this (by decide)
end
