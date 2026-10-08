-- Prove2me | solution 1 for ErschlerZheng.sec_evalWord_zetaWord_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:05:58.840645+00:00
-- url     : https://prove2.me/submissions/7b218a76-3f0e-4bd7-be5d-549a8fd6b9f1

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

theorem rootSwap_mul (g h : BinaryTreeAut) :
    rootSwap (g * h) = xor (rootSwap g) (rootSwap h) := by
  have : [false] <• (g * h) = [xor (rootSwap g) (rootSwap h)] := by
    rw [vertex_smul_mul, singleton_smul g, singleton_smul h]
    simp
  show decide ([false] <• (g * h) = [true]) = _
  rw [this]
  cases rootSwap g <;> cases rootSwap h <;> rfl

theorem rootSwap_one : rootSwap 1 = false := by
  unfold rootSwap; simp

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem grigA_mul_grigA_mul (x : BinaryTreeAut) : grigA * (grigA * x) = x := by
  rw [← mul_assoc, grigA_mul_self, one_mul]

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

theorem rootSwap_gen (ω : ℕ → Fin 3) (γ : BCD) : rootSwap (gen ω γ) = false := by
  unfold rootSwap
  rw [vertex_smul_gen]
  simp [genFun]

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

/-! ### Words -/

theorem evalWord_append (ω : ℕ → Fin 3) (k : ℕ) (u v : List Gen4) :
    evalWord ω k (u ++ v) = evalWord ω k u * evalWord ω k v := by
  simp [evalWord, List.map_append, List.prod_append]

theorem evalWord_nil (ω : ℕ → Fin 3) (k : ℕ) : evalWord ω k [] = 1 := rfl

/-- The value of a pair `aγ` in `G_{𝔰^k ω}`. -/
def pairLetter : APair → BCD
  | .ab => .b
  | .ac => .c
  | .ad => .d

theorem evalWord_toWord (ω : ℕ → Fin 3) (k : ℕ) (p : APair) :
    evalWord ω k p.toWord = grigA * gen (shiftSeq ω k) (pairLetter p) := by
  cases p <;> simp [evalWord, APair.toWord, pairLetter]

theorem evalWord_flatMap_cons (ω : ℕ → Fin 3) (k : ℕ) (p : APair) (w : List APair) :
    evalWord ω k ((p :: w).flatMap APair.toWord) =
      evalWord ω k p.toWord * evalWord ω k (w.flatMap APair.toWord) := by
  rw [List.flatMap_cons, evalWord_append]

theorem evalWord_flatMap_append (ω : ℕ → Fin 3) (k : ℕ) (u w : List APair) :
    evalWord ω k ((u ++ w).flatMap APair.toWord) =
      evalWord ω k (u.flatMap APair.toWord) * evalWord ω k (w.flatMap APair.toWord) := by
  rw [List.flatMap_append, evalWord_append]

theorem count_a_flatMap_toWord (w : List APair) :
    (w.flatMap APair.toWord).count .a = w.length := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    cases p <;> simp [APair.toWord] <;> omega

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

/-- `g` has root swap `e` and level-1 sections `s0` (at `0`) and `s1` (at `1`). -/
def Dec3 (g : BinaryTreeAut) (e : Bool) (s0 s1 : BinaryTreeAut) : Prop :=
  rootSwap g = e ∧ sec g [false] = s0 ∧ sec g [true] = s1

theorem dec_congr {g : BinaryTreeAut} {e : Bool} {s0 s1 t0 t1 : BinaryTreeAut}
    (h : Dec3 g e s0 s1) (h0 : s0 = t0) (h1 : s1 = t1) : Dec3 g e t0 t1 := by
  subst h0 h1; exact h

theorem dec_mul {g h : BinaryTreeAut} {e f : Bool} {g0 g1 h0 h1 : BinaryTreeAut}
    (hg : Dec3 g e g0 g1) (hh : Dec3 h f h0 h1) :
    Dec3 (g * h) (xor e f) (g0 * (if e then h1 else h0)) (g1 * (if e then h0 else h1)) := by
  obtain ⟨he, hg0, hg1⟩ := hg
  obtain ⟨hf, hh0, hh1⟩ := hh
  refine ⟨by rw [rootSwap_mul, he, hf], ?_, ?_⟩
  · rw [sec_mul, hg0, singleton_smul, he]; cases e <;> simp [hh0, hh1]
  · rw [sec_mul, hg1, singleton_smul, he]; cases e <;> simp [hh0, hh1]

theorem dec_one : Dec3 1 false 1 1 := ⟨rootSwap_one, sec_one _, sec_one _⟩

theorem dec_grigA : Dec3 grigA true 1 1 := ⟨rootSwap_grigA, sec_grigA _, sec_grigA _⟩

theorem dec_gen (ω : ℕ → Fin 3) (γ : BCD) :
    Dec3 (gen ω γ) false (letterElt (ω 0) γ) (gen (shiftSeq ω 1) γ) :=
  ⟨rootSwap_gen ω γ, sec_gen_false ω γ, sec_gen_true ω γ⟩

/-- The value `aγ` of a pair in `G_{𝔰^n ω}`. -/
theorem dec_pair (ω : ℕ → Fin 3) (n : ℕ) (γ : BCD) :
    Dec3 (grigA * gen (shiftSeq ω n) γ) true (gen (shiftSeq ω (n + 1)) γ)
      (letterElt (ω n) γ) := by
  have := dec_mul dec_grigA (dec_gen (shiftSeq ω n) γ)
  simp only [Bool.xor_false, if_true, one_mul] at this
  rw [shiftSeq_shiftSeq, show 1 + n = n + 1 by omega,
    show shiftSeq ω n 0 = ω n by simp [shiftSeq]] at this
  exact this

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨k, hk⟩
  interval_cases k <;> simp

end ZetaDev

end ErschlerZheng
end

section
/-!
# A5: (2.3), corrected, p. 15

For a word `w` over `{ab, ac, ad}`, `ζ_{ω_n}(w)` evaluated in `G_{𝔰^n ω}` has sections
`(awa, w)` when it has an even number of `a`, and swaps level 1 with sections `(aw, wa)` when odd.
-/

open scoped RightActions
set_option linter.unusedSimpArgs false
open Garrido

namespace ErschlerZheng

namespace ZetaDev

open GrigBasic

/-- (2.3) for a single pair. -/
theorem dec_zetaPair (ω : ℕ → Fin 3) (n : ℕ) (p : APair) :
    Dec3 (evalWord ω n ((zetaPair (ω n) p).flatMap APair.toWord))
      (Nat.bodd (zetaPair (ω n) p).length)
      (grigA * evalWord ω (n + 1) p.toWord *
        (if Nat.bodd (zetaPair (ω n) p).length then 1 else grigA))
      (evalWord ω (n + 1) p.toWord *
        (if Nat.bodd (zetaPair (ω n) p).length then grigA else 1)) := by
  have Db := dec_pair ω n .b
  have Dc := dec_pair ω n .c
  have Dd := dec_pair ω n .d
  rw [evalWord_toWord]
  rcases fin3_cases (ω n) with hi | hi | hi <;> rw [hi] at Db Dc Dd ⊢ <;>
    simp [letterElt, letterValue, BCD.killedBy] at Db Dc Dd <;>
    cases p <;>
    simp only [zetaPair, evalWord_flatMap_cons, List.flatMap_nil, evalWord_nil, evalWord_toWord,
      pairLetter, List.length_cons, List.length_nil] at Db Dc Dd ⊢
  -- i = 0
  · have := dec_mul Db (dec_mul Db dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]
  · have := dec_mul Dc (dec_mul Dc dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]
  · have := dec_mul Db (dec_mul Dd (dec_mul Dc dec_one))
    refine dec_congr this ?_ ?_ <;>
      simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd, gen_b_mul_c]
  -- i = 1
  · have := dec_mul Db (dec_mul Db dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]
  · have := dec_mul Dd (dec_mul Dc (dec_mul Db dec_one))
    refine dec_congr this ?_ ?_ <;>
      simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd, gen_d_mul_b]
  · have := dec_mul Dd (dec_mul Dd dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]
  -- i = 2
  · have := dec_mul Dc (dec_mul Db (dec_mul Dd dec_one))
    refine dec_congr this ?_ ?_ <;>
      simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd, gen_c_mul_d]
  · have := dec_mul Dc (dec_mul Dc dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]
  · have := dec_mul Dd (dec_mul Dd dec_one)
    refine dec_congr this ?_ ?_ <;> simp [mul_assoc, grigA_mul_grigA_mul, Nat.bodd]

/-- (2.3) for every word over `{ab, ac, ad}`. -/
theorem dec_zetaWord (ω : ℕ → Fin 3) (n : ℕ) (w : List APair) :
    Dec3 (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord))
      (Nat.bodd (zetaWord (ω n) w).length)
      (grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) *
        (if Nat.bodd (zetaWord (ω n) w).length then 1 else grigA))
      (evalWord ω (n + 1) (w.flatMap APair.toWord) *
        (if Nat.bodd (zetaWord (ω n) w).length then grigA else 1)) := by
  induction w with
  | nil =>
    simp only [zetaWord, List.flatMap_nil, evalWord_nil, List.length_nil]
    refine dec_congr dec_one ?_ ?_ <;> simp [Nat.bodd, grigA_mul_self]
  | cons p w ih =>
    have hz : zetaWord (ω n) (p :: w) = zetaPair (ω n) p ++ zetaWord (ω n) w := by
      simp [zetaWord]
    rw [hz, evalWord_flatMap_append, List.length_append, Nat.bodd_add, evalWord_flatMap_cons]
    have := dec_mul (dec_zetaPair ω n p) ih
    refine dec_congr this ?_ ?_ <;>
    · cases Nat.bodd (zetaPair (ω n) p).length <;> cases Nat.bodd (zetaWord (ω n) w).length <;>
        simp [mul_assoc, grigA_mul_grigA_mul]

end ZetaDev

end ErschlerZheng
end

section
open scoped RightActions
set_option linter.unusedSimpArgs false
open Garrido
open ErschlerZheng
open GrigBasic ZetaDev in
theorem solution (ω : ℕ → Fin 3) (n : ℕ) (w : List APair) :
    (Even (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
      evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord) ∈ levelStab ⊤ 1 ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
          Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
          evalWord ω (n + 1) (w.flatMap APair.toWord)) ∧
    (Odd (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
      [false] <• evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord) = [true] ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
          Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
          evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA) := by
  obtain ⟨h0, h1, h2⟩ := dec_zetaWord ω n w
  rw [count_a_flatMap_toWord]
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · have hb : Nat.bodd (zetaWord (ω n) w).length = false := by
      have := Nat.mod_two_of_bodd (zetaWord (ω n) w).length
      rw [Nat.even_iff] at he
      cases h : Nat.bodd (zetaWord (ω n) w).length <;> simp_all
    rw [hb] at h0 h1 h2
    simp only [if_false, Bool.false_eq_true, mul_one] at h1 h2
    refine ⟨?_, h1, h2⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hv
    rw [singleton_smul, h0]
    simp
  · have hb : Nat.bodd (zetaWord (ω n) w).length = true := by
      have := Nat.mod_two_of_bodd (zetaWord (ω n) w).length
      rw [Nat.odd_iff] at ho
      cases h : Nat.bodd (zetaWord (ω n) w).length <;> simp_all
    rw [hb] at h0 h1 h2
    simp only [if_true, mul_one] at h1 h2
    refine ⟨?_, h1, h2⟩
    rw [singleton_smul, h0]
    rfl
end
