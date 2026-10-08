-- Prove2me | solution 1 for ErschlerZheng.vertex_smul_eq_smul_seqG_of_mem_fSet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T05:37:47.769189+00:00
-- url     : https://prove2.me/submissions/b1cf1287-70b7-48bb-8363-3860f77953d1

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne
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

theorem rootSwap_inv (g : BinaryTreeAut) : rootSwap g⁻¹ = rootSwap g := by
  have := rootSwap_mul g g⁻¹
  rw [mul_inv_cancel, rootSwap_one] at this
  cases h1 : rootSwap g <;> cases h2 : rootSwap g⁻¹ <;> simp_all

theorem cons_smul (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    (x :: u) <• g = xor x (rootSwap g) :: (u <• sec g [x]) := by
  have := append_vertex_smul g [x] u
  rw [singleton_smul] at this
  exact this

/-- An automorphism is determined by its root swap and its two sections at level 1. -/
theorem ext_of_rootSwap_sec {g h : BinaryTreeAut} (h0 : rootSwap g = rootSwap h)
    (hf : sec g [false] = sec h [false]) (ht : sec g [true] = sec h [true]) : g = h := by
  have key : ∀ v : List Bool, v <• g = v <• h := by
    intro v
    cases v with
    | nil => rw [nil_smul, nil_smul]
    | cons x u =>
      rw [cons_smul, cons_smul, h0]
      cases x
      · rw [hf]
      · rw [ht]
  have : g⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

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

theorem dec_inv {g : BinaryTreeAut} {e : Bool} {g0 g1 : BinaryTreeAut} (hg : Dec3 g e g0 g1) :
    Dec3 g⁻¹ e (if e then g1⁻¹ else g0⁻¹) (if e then g0⁻¹ else g1⁻¹) := by
  obtain ⟨he, hg0, hg1⟩ := hg
  refine ⟨by rw [rootSwap_inv, he], ?_, ?_⟩
  · rw [sec_inv, singleton_smul, rootSwap_inv, he]; cases e <;> simp [hg0, hg1]
  · rw [sec_inv, singleton_smul, rootSwap_inv, he]; cases e <;> simp [hg0, hg1]

theorem dec_one : Dec3 1 false 1 1 := ⟨rootSwap_one, sec_one _, sec_one _⟩

theorem dec_grigA : Dec3 grigA true 1 1 := ⟨rootSwap_grigA, sec_grigA _, sec_grigA _⟩

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨k, hk⟩
  interval_cases k <;> simp

end ZetaDev

end ErschlerZheng
end

section
/-!
# A7: the substitutions act on group elements (p. 15), under the tail hypothesis

Route. By (2.3) (A5, imported), `g = ζ_{ω_n}(w)` evaluated in `G_{𝔰^n ω}` is determined by its
root swap `β(w)` and by `W = w` evaluated in `G_{𝔰^{n+1} ω}`: its level-1 sections are
`(aWa, W)` or `(aW, Wa)`. It remains to see that `β(w)` is a function of `W`. For every level
`k`, `σ_k(g) = Σ_{|v| = k} [g_v swaps level 1] mod 2` is a homomorphism `Aut(T) → ℤ/2`, with
`σ_0(a) = 1`, `σ_{k+1}(a) = 0`, `σ_0(γ_ω) = 0`, `σ_{k+1}(γ_ω) = ω_k(γ)`. The parity `β` counts
the pairs `a κ` with `κ` the generator killed by `ω_n`; under the tail hypothesis it is
`σ_0 + Σ_{j ∈ J} σ_{j+1}` of `W` for a set `J` of one level (where `ω_n` recurs) or two levels
(where the two other letters occur).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace ZetaHatDev

open GrigBasic ZetaDev

/-! ### Level parities -/

/-- `1` if `g` swaps level 1, else `0`. -/
def bit (g : BinaryTreeAut) : ZMod 2 := if rootSwap g then 1 else 0

theorem bit_mul (g h : BinaryTreeAut) : bit (g * h) = bit g + bit h := by
  unfold bit
  rw [rootSwap_mul]
  cases rootSwap g <;> cases rootSwap h <;> decide

theorem bit_one : bit 1 = 0 := by simp [bit, rootSwap_one]

/-! ### The free-group words -/

theorem evalFree_of (ω : ℕ → Fin 3) (k : ℕ) (p : APair) :
    evalFree ω k (FreeGroup.of p) = evalWord ω k p.toWord := by
  simp [evalFree]

theorem evalFree_prod_map_of (ω : ℕ → Fin 3) (k : ℕ) (u : List APair) :
    evalFree ω k (u.map FreeGroup.of).prod = evalWord ω k (u.flatMap APair.toWord) := by
  induction u with
  | nil => simp [evalWord_nil]
  | cons p u ih => rw [List.map_cons, List.prod_cons, map_mul, ih, evalFree_of,
      evalWord_flatMap_cons]

theorem evalFree_zetaFree_of (ω : ℕ → Fin 3) (n : ℕ) (p : APair) :
    evalFree ω n (zetaFree (ω n) (FreeGroup.of p)) =
      evalWord ω n ((zetaWord (ω n) [p]).flatMap APair.toWord) := by
  rw [show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]]
  simp only [zetaFree, FreeGroup.lift_apply_of]
  exact evalFree_prod_map_of ω n _

/-- (2.3) for free-group words, from (2.3) for single pairs (A5). -/
theorem dec_evalFree (ω : ℕ → Fin 3) (n : ℕ) (w : FreeGroup APair) :
    Dec3 (evalFree ω n (zetaFree (ω n) w)) (rootSwap (evalFree ω n (zetaFree (ω n) w)))
      (grigA * evalFree ω (n + 1) w *
        (if rootSwap (evalFree ω n (zetaFree (ω n) w)) then 1 else grigA))
      (evalFree ω (n + 1) w *
        (if rootSwap (evalFree ω n (zetaFree (ω n) w)) then grigA else 1)) := by
  induction w using FreeGroup.induction_on with
  | C1 =>
    simp only [map_one]
    refine dec_congr dec_one ?_ ?_ <;> simp [rootSwap_one, grigA_mul_self]
  | of p =>
    have hA := sec_evalWord_zetaWord_eq ω n [p]
    have hW : evalWord ω (n + 1) ([p].flatMap APair.toWord) = evalFree ω (n + 1) (FreeGroup.of p) := by
      rw [evalFree_of]; simp
    rw [evalFree_zetaFree_of, ← hW]
    set g := evalWord ω n ((zetaWord (ω n) [p]).flatMap APair.toWord)
    rcases Nat.even_or_odd (((zetaWord (ω n) [p]).flatMap APair.toWord).count .a) with he | ho
    · obtain ⟨hst, h0, h1⟩ := hA.1 he
      have hr : rootSwap g = false := by
        have := (Subgroup.mem_inf.mp hst).2 [false] rfl
        unfold rootSwap
        rw [this]
        decide
      refine ⟨rfl, ?_, ?_⟩ <;> simp [hr, h0, h1]
    · obtain ⟨hsw, h0, h1⟩ := hA.2 ho
      have hr : rootSwap g = true := by unfold rootSwap; rw [hsw]; decide
      refine ⟨rfl, ?_, ?_⟩ <;> simp [hr, h0, h1]
  | inv_of p ih =>
    have := dec_inv ih
    simp only [map_inv, rootSwap_inv] at this ⊢
    refine dec_congr this ?_ ?_ <;>
    · cases rootSwap (evalFree ω n (zetaFree (ω n) (FreeGroup.of p))) <;>
        simp [mul_inv_rev, grigA_inv, mul_assoc]
  | mul x y ihx ihy =>
    have := dec_mul ihx ihy
    simp only [map_mul, rootSwap_mul] at this ⊢
    refine dec_congr this ?_ ?_ <;>
    · cases rootSwap (evalFree ω n (zetaFree (ω n) x)) <;>
        cases rootSwap (evalFree ω n (zetaFree (ω n) y)) <;>
        simp [mul_assoc, grigA_mul_grigA_mul]

/-! ### The parity is a function of the element -/

theorem bodd_length_zetaPair (i : Fin 3) (p : APair) :
    (if Nat.bodd (zetaPair i p).length then (1 : ZMod 2) else 0) =
      if pairLetter p = BCD.killedBy i then 1 else 0 := by
  rcases fin3_cases i with rfl | rfl | rfl <;> cases p <;> rfl

theorem bit_evalFree_zetaFree_of (ω : ℕ → Fin 3) (n : ℕ) (p : APair) :
    bit (evalFree ω n (zetaFree (ω n) (FreeGroup.of p))) =
      if pairLetter p = BCD.killedBy (ω n) then 1 else 0 := by
  rw [← bodd_length_zetaPair, evalFree_zetaFree_of]
  have hd := (dec_evalFree ω n (FreeGroup.of p)).1
  have hA := sec_evalWord_zetaWord_eq ω n [p]
  rw [count_a_flatMap_toWord, show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]] at hA
  rw [show zetaWord (ω n) [p] = zetaPair (ω n) p by simp [zetaWord]]
  unfold bit rootSwap
  rcases Nat.even_or_odd (zetaPair (ω n) p).length with he | ho
  · have hb : Nat.bodd (zetaPair (ω n) p).length = false := by
      have := Nat.mod_two_of_bodd (zetaPair (ω n) p).length
      rw [Nat.even_iff] at he
      cases h : Nat.bodd (zetaPair (ω n) p).length <;> simp_all
    have := (Subgroup.mem_inf.mp (hA.1 he).1).2 [false] rfl
    rw [this, hb]
    decide
  · have hb : Nat.bodd (zetaPair (ω n) p).length = true := by
      have := Nat.mod_two_of_bodd (zetaPair (ω n) p).length
      rw [Nat.odd_iff] at ho
      cases h : Nat.bodd (zetaPair (ω n) p).length <;> simp_all
    rw [(hA.2 ho).1, hb]
    decide

end ZetaHatDev

open GrigBasic ZetaDev ZetaHatDev

end ErschlerZheng
end

section
/-!
# The index sets `W^n_k` and `V^j_k` (Erschler–Zheng p. 37)

`|W^n_k| = 2^{k/D}` for `D ∣ n`, `D ∣ k`; `|V^j_k| = 2^{k/D}` and every `v ∈ V^j_k` ends with `0`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrW

theorem frM_spec (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (ℓ : ℕ) :
    frM D ω ℓ + 3 ≤ D ∧ ω (ℓ * D + frM D ω ℓ) = 2 ∧ ω (ℓ * D + frM D ω ℓ + 2) = 1 ∧
      (ω (ℓ * D + frM D ω ℓ + 1) = 0 ∨ ω (ℓ * D + frM D ω ℓ + 1) = 1) := by
  have hne : {m | m + 3 ≤ D ∧ ω (ℓ * D + m) = 2 ∧ ω (ℓ * D + m + 2) = 1 ∧
      (ω (ℓ * D + m + 1) = 0 ∨ ω (ℓ * D + m + 1) = 1)}.Nonempty := hω ℓ
  exact Nat.sInf_mem hne

end ConstrW

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

theorem iota_mul (g h : BinaryTreeAut) (u : List Bool) :
    iota g u * iota h u = iota (g * h) u := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun g u (iotaFun h u w) = iotaFun (g * h) u w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp
  · simp [hw]

theorem iota_one (u : List Bool) : iota 1 u = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun 1 u w = w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp
  · simp [hw]

theorem iota_inv (g : BinaryTreeAut) (u : List Bool) : (iota g u)⁻¹ = iota g⁻¹ u := by
  apply inv_eq_of_mul_eq_one_right
  rw [iota_mul, mul_inv_cancel, iota_one]

theorem iota_nil (g : BinaryTreeAut) : iota g [] = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun g [] w = _
  simp [iotaFun]

theorem iota_iota (g : BinaryTreeAut) (u v : List Bool) :
    iota (iota g v) u = iota g (u ++ v) := by
  apply Subtype.ext
  apply Equiv.ext
  intro w
  show iotaFun (iota g v) u w = iotaFun g (u ++ v) w
  unfold iotaFun
  by_cases hw : u <+: w
  · obtain ⟨t, rfl⟩ := hw
    simp only [List.prefix_append, if_true, List.drop_left', List.prefix_append_right_inj]
    show u ++ iotaFun g v t = _
    unfold iotaFun
    by_cases ht : v <+: t
    · obtain ⟨s, rfl⟩ := ht
      simp
    · simp [ht]
  · have : ¬ u ++ v <+: w := fun h => hw ((List.prefix_append u v).trans h)
    simp [hw, this]

theorem vertex_smul_iota (g : BinaryTreeAut) (u v : List Bool) :
    v <• iota g u = if u <+: v then u ++ (v.drop u.length <• g) else v := by
  rw [vertex_smul_def, iota_inv]
  rfl

theorem append_smul_iota (g : BinaryTreeAut) (u w : List Bool) :
    (u ++ w) <• iota g u = u ++ (w <• g) := by
  rw [vertex_smul_iota, if_pos (List.prefix_append u w)]
  simp

theorem smul_iota_of_not_prefix (g : BinaryTreeAut) (u v : List Bool) (h : ¬ u <+: v) :
    v <• iota g u = v := by
  rw [vertex_smul_iota, if_neg h]

theorem sec_iota_self (g : BinaryTreeAut) (u : List Bool) : sec (iota g u) u = g := by
  apply sec_unique
  intro w
  rw [append_smul_iota]
  have : u <• iota g u = u := by
    have := append_smul_iota g u []
    simpa [nil_smul] using this
  rw [this]

/-- `ι(g, x)` for a first-level vertex `x`: no root swap, section `g` at `x`, `1` at `!x`. -/
theorem dec_iota (g : BinaryTreeAut) (x : Bool) :
    Dec3 (iota g [x]) false (if x then 1 else g) (if x then g else 1) := by
  have h1 : ∀ y : Bool, [y] <• iota g [x] = [y] := by
    intro y
    by_cases hy : y = x
    · subst hy
      have := append_smul_iota g [y] []
      simpa [nil_smul] using this
    · apply smul_iota_of_not_prefix
      simp [Ne.symm hy]
  refine ⟨?_, ?_, ?_⟩
  · unfold rootSwap
    rw [h1]
    simp
  · cases x
    · simpa using sec_iota_self g [false]
    · simp only [if_true]
      apply sec_unique
      intro w
      rw [smul_iota_of_not_prefix _ _ _ (by simp), h1]
      rfl
  · cases x
    · simp only [Bool.false_eq_true, if_false]
      apply sec_unique
      intro w
      rw [smul_iota_of_not_prefix _ _ _ (by simp), h1]
      rfl
    · simpa using sec_iota_self g [true]

/-- The element with sections `g` at `0` and `h` at `1` and no root swap. -/
def pairElt (g h : BinaryTreeAut) : BinaryTreeAut := iota g [false] * iota h [true]

theorem dec_pairElt (g h : BinaryTreeAut) : Dec3 (pairElt g h) false g h := by
  have := dec_mul (dec_iota g false) (dec_iota h true)
  simpa [pairElt] using this

theorem eq_of_dec {g h : BinaryTreeAut} {e : Bool} {s0 s1 : BinaryTreeAut}
    (hg : Dec3 g e s0 s1) (hh : Dec3 h e s0 s1) : g = h :=
  ext_of_rootSwap_sec (hg.1.trans hh.1.symm) (hg.2.1.trans hh.2.1.symm)
    (hg.2.2.trans hh.2.2.symm)

theorem pairElt_mul (g h g' h' : BinaryTreeAut) :
    pairElt g h * pairElt g' h' = pairElt (g * g') (h * h') := by
  apply eq_of_dec (dec_mul (dec_pairElt g h) (dec_pairElt g' h'))
  simpa using dec_pairElt (g * g') (h * h')

theorem pairElt_one : pairElt 1 1 = 1 := by
  simp [pairElt, iota_one]

theorem grigA_conj_pairElt (g h : BinaryTreeAut) :
    grigA * pairElt g h * grigA = pairElt h g := by
  apply eq_of_dec (dec_mul (dec_mul dec_grigA (dec_pairElt g h)) dec_grigA)
  simpa using dec_pairElt h g

theorem gen_eq_pairElt (ω : ℕ → Fin 3) (ℓ : ℕ) (γ : BCD) :
    gen (shiftSeq ω ℓ) γ = pairElt (letterElt (ω ℓ) γ) (gen (shiftSeq ω (ℓ + 1)) γ) := by
  apply eq_of_dec _ (dec_pairElt _ _)
  refine ⟨rootSwap_gen _ _, ?_, ?_⟩
  · rw [sec_gen_false]; simp [shiftSeq]
  · rw [sec_gen_true, shiftSeq_shiftSeq, Nat.add_comm]

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

/-- The value of a word under a letter map. -/
def evL (φ : Gen4 → BinaryTreeAut) (w : List Gen4) : BinaryTreeAut := (w.map φ).prod

theorem evL_nil (φ : Gen4 → BinaryTreeAut) : evL φ [] = 1 := rfl

theorem evL_cons (φ : Gen4 → BinaryTreeAut) (l : Gen4) (w : List Gen4) :
    evL φ (l :: w) = φ l * evL φ w := by
  simp [evL]

theorem evL_append (φ : Gen4 → BinaryTreeAut) (u w : List Gen4) :
    evL φ (u ++ w) = evL φ u * evL φ w := by
  simp [evL]

theorem evL_flatMap (φ : Gen4 → BinaryTreeAut) (g : Gen4 → List Gen4) (w : List Gen4) :
    evL φ (w.flatMap g) = evL (fun l => evL φ (g l)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.flatMap_cons, evL_append, evL_cons, ih]

theorem evL_reverse (φ : Gen4 → BinaryTreeAut) (hφ : ∀ l, φ l * φ l = 1) (w : List Gen4) :
    evL φ w.reverse = (evL φ w)⁻¹ := by
  induction w with
  | nil => simp [evL]
  | cons l w ih =>
    rw [List.reverse_cons, evL_append, ih, evL_cons φ l w, mul_inv_rev]
    congr 1
    rw [evL_cons, evL_nil, mul_one]
    exact (inv_eq_of_mul_eq_one_right (hφ l)).symm

theorem evalWord_eq_evL (ω : ℕ → Fin 3) (k : ℕ) (w : List Gen4) :
    evalWord ω k w = evL (lm grigA (gen (shiftSeq ω k))) w := by
  unfold evalWord evL
  congr 1

theorem evL_congr {φ ψ : Gen4 → BinaryTreeAut} (h : ∀ l, φ l = ψ l) (w : List Gen4) :
    evL φ w = evL ψ w := by
  unfold evL
  congr 1
  exact List.map_congr_left fun l _ => h l

/-- The commutator word `p q p^R q^R` (all letters are involutions). -/
def commW (p q : List Gen4) : List Gen4 := p ++ q ++ p.reverse ++ q.reverse

theorem evL_commW (φ : Gen4 → BinaryTreeAut) (hφ : ∀ l, φ l * φ l = 1) (p q : List Gen4) :
    evL φ (commW p q) = ⁅evL φ p, evL φ q⁆ := by
  rw [commW, evL_append, evL_append, evL_append, evL_reverse φ hφ, evL_reverse φ hφ,
    commutatorElement_def]

/-- The letter map of the invariant: `a ↦ z`, `γ ↦ A` if `e γ`, else `1`. -/
def killMap (z A : BinaryTreeAut) (e : BCD → Bool) : Gen4 → BinaryTreeAut :=
  lm z fun γ => if e γ then A else 1

/-- The invariant: `w` evaluates to `1` under every `killMap z A e` with `z, A` involutions. -/
def Kill (e : BCD → Bool) (w : List Gen4) : Prop :=
  ∀ z A : BinaryTreeAut, z * z = 1 → A * A = 1 → evL (killMap z A e) w = 1

/-! ### The lift -/

/-- The lift of a letter: towards `1` (`x = true`): `a ↦ a y a`, `γ ↦ γ`; towards `0`:
`a ↦ y`, `γ ↦ a γ a`. -/
def liftL (x : Bool) (y : BCD) : Gen4 → List Gen4
  | .a => if x then [.a, bcdGen y, .a] else [bcdGen y]
  | .b => if x then [.b] else [.a, .b, .a]
  | .c => if x then [.c] else [.a, .c, .a]
  | .d => if x then [.d] else [.a, .d, .a]

theorem liftL_palindrome (x : Bool) (y : BCD) (l : Gen4) : (liftL x y l).reverse = liftL x y l := by
  cases l <;> cases x <;> simp [liftL]

theorem flatMap_reverse_of_palindrome (g : Gen4 → List Gen4) (hg : ∀ l, (g l).reverse = g l)
    (w : List Gen4) : w.reverse.flatMap g = (w.flatMap g).reverse := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.reverse_cons, List.flatMap_append, ih]
    simp [hg]

theorem lift_commW (x : Bool) (y : BCD) (p q : List Gen4) :
    (commW p q).flatMap (liftL x y) = commW (p.flatMap (liftL x y)) (q.flatMap (liftL x y)) := by
  simp only [commW, List.flatMap_append]
  rw [flatMap_reverse_of_palindrome _ (liftL_palindrome x y),
    flatMap_reverse_of_palindrome _ (liftL_palindrome x y)]

theorem bcdGen_ne_a (y : BCD) : bcdGen y ≠ .a := by cases y <;> simp [bcdGen]

theorem lift_counts (x : Bool) (y : BCD) (w : List Gen4) :
    (if x then (w.flatMap (liftL x y)).length = 2 * w.count .a + w.length ∧
        (w.flatMap (liftL x y)).count .a = 2 * w.count .a
      else (w.flatMap (liftL x y)).length + 2 * w.count .a = 3 * w.length ∧
        (w.flatMap (liftL x y)).count .a + 2 * w.count .a = 2 * w.length) := by
  have hy : List.count Gen4.a [bcdGen y] = 0 := by
    cases y <;> rfl
  induction w with
  | nil => cases x <;> simp
  | cons l w ih =>
    rw [List.flatMap_cons, List.length_append, List.count_append, List.count_cons,
      List.length_cons]
    cases x <;> cases l <;> simp only [liftL, if_true, Bool.false_eq_true, if_false] at ih ⊢ <;>
      simp [List.count_cons, List.count_nil, hy, bcdGen_ne_a] at ih ⊢ <;> omega

theorem lift_length (x : Bool) (y : BCD) (w : List Gen4) (hw : 2 * w.count .a = w.length) :
    (w.flatMap (liftL x y)).length = 2 * w.length ∧
      2 * (w.flatMap (liftL x y)).count .a = (w.flatMap (liftL x y)).length := by
  have := lift_counts x y w
  cases x
  · simp only [Bool.false_eq_true, if_false] at this; omega
  · simp only [if_true] at this; omega

theorem evL_liftL_true (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (l : Gen4) :
    evL (lm grigA (gen (shiftSeq ω ℓ))) (liftL true y l) =
      pairElt (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ)) l)
        (lm grigA (gen (shiftSeq ω (ℓ + 1))) l) := by
  cases l <;> simp only [liftL, if_true, evL_cons, evL_nil, mul_one, lm_a, lm_b, lm_c, lm_d,
    lm_bcdGen]
  · rw [gen_eq_pairElt ω ℓ, ← mul_assoc, grigA_conj_pairElt]
    simp [letterElt, hy]
  all_goals exact gen_eq_pairElt ω ℓ _

theorem evL_liftL_false (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (l : Gen4) :
    evL (lm grigA (gen (shiftSeq ω ℓ))) (liftL false y l) =
      pairElt (lm grigA (gen (shiftSeq ω (ℓ + 1)))  l)
        (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ)) l) := by
  cases l <;> simp only [liftL, Bool.false_eq_true, if_false, evL_cons, evL_nil, mul_one, lm_a,
    lm_b, lm_c, lm_d, lm_bcdGen]
  · rw [gen_eq_pairElt ω ℓ]
    simp [letterElt, hy]
  all_goals rw [gen_eq_pairElt ω ℓ, ← mul_assoc, grigA_conj_pairElt]

/-- The lifting identity, towards `1`. -/
theorem evalWord_lift_true (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (w : List Gen4) :
    evalWord ω ℓ (w.flatMap (liftL true y)) =
      pairElt (evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w)
        (evalWord ω (ℓ + 1) w) := by
  rw [evalWord_eq_evL, evL_flatMap, evalWord_eq_evL]
  induction w with
  | nil => simp [evL, pairElt_one]
  | cons l w ih =>
    rw [evL_cons, ih, evL_cons, evL_cons, ← pairElt_mul, evL_liftL_true ω ℓ y hy]

/-- The lifting identity, towards `0`. -/
theorem evalWord_lift_false (ω : ℕ → Fin 3) (ℓ : ℕ) (y : BCD) (hy : letterValue (ω ℓ) y = true)
    (w : List Gen4) :
    evalWord ω ℓ (w.flatMap (liftL false y)) =
      pairElt (evalWord ω (ℓ + 1) w)
        (evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w) := by
  rw [evalWord_eq_evL, evL_flatMap, evalWord_eq_evL]
  induction w with
  | nil => simp [evL, pairElt_one]
  | cons l w ih =>
    rw [evL_cons, ih, evL_cons, evL_cons, ← pairElt_mul, evL_liftL_false ω ℓ y hy]


/-! ### The invariant `Kill` under lifts -/

theorem evL_mem_pair (ψ : Gen4 → BinaryTreeAut) (A : BinaryTreeAut) (hA : A * A = 1)
    (hψ : ∀ l, ψ l = 1 ∨ ψ l = A) (w : List Gen4) : evL ψ w = 1 ∨ evL ψ w = A := by
  induction w with
  | nil => left; rfl
  | cons l w ih =>
    rw [evL_cons]
    rcases hψ l with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> simp [hA]

theorem evL_commW_of_pair (ψ : Gen4 → BinaryTreeAut) (A : BinaryTreeAut) (hA : A * A = 1)
    (hψ : ∀ l, ψ l = 1 ∨ ψ l = A) (p q : List Gen4) : evL ψ (commW p q) = 1 := by
  have hinv : ∀ l, ψ l * ψ l = 1 := by
    intro l; rcases hψ l with h | h <;> rw [h]; simp; exact hA
  rw [evL_commW ψ hinv]
  rcases evL_mem_pair ψ A hA hψ p with h | h <;> rcases evL_mem_pair ψ A hA hψ q with h' | h' <;>
    rw [h, h'] <;> simp [commutatorElement_def]

theorem evL_conj (z : BinaryTreeAut) (hz : z * z = 1) (ψ : Gen4 → BinaryTreeAut) (w : List Gen4) :
    evL (fun l => z * ψ l * z) w = z * evL ψ w * z := by
  induction w with
  | nil => simp [evL, hz]
  | cons l w ih =>
    rw [evL_cons, evL_cons, ih]
    calc z * ψ l * z * (z * evL ψ w * z) = z * ψ l * (z * z) * evL ψ w * z := by
          simp only [mul_assoc]
      _ = z * (ψ l * evL ψ w) * z := by rw [hz]; simp only [mul_one, mul_assoc]

theorem kill_lift (e e' : BCD → Bool) (x : Bool) (y : BCD) (p q : List Gen4)
    (h : e' y = false ∨ (e' = e ∧ Kill e (commW p q))) :
    Kill e' ((commW p q).flatMap (liftL x y)) := by
  intro z A hz hA
  have hz' : ∀ X : BinaryTreeAut, z * (z * X) = X := fun X => by rw [← mul_assoc, hz, one_mul]
  rw [evL_flatMap]
  by_cases hy : e' y = true
  · rcases h with h | ⟨rfl, hk⟩
    · rw [hy] at h; exact absurd h (by simp)
    cases x
    · -- towards `0`: `a ↦ A`, `γ ↦ z (A or 1) z`
      have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      have key : ∀ l, evL (killMap z A e') (liftL false y l) =
          z * killMap (z * A * z) A e' l * z := by
        intro l
        cases l <;> simp [liftL, killMap, evL_cons, evL_nil, hy, mul_assoc, hz, hz']
      rw [evL_congr key, evL_conj z hz, hk (z * A * z) A hzAz hA]
      simp [hz]
    · have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      have key : ∀ l, evL (killMap z A e') (liftL true y l) = killMap (z * A * z) A e' l := by
        intro l
        cases l <;> simp [liftL, killMap, evL_cons, evL_nil, hy, mul_assoc]
      rw [evL_congr key, hk (z * A * z) A hzAz hA]
  · have hy' : e' y = false := by simpa using hy
    cases x
    · have hzAz : z * A * z * (z * A * z) = 1 := by
        calc z * A * z * (z * A * z) = z * A * (z * z) * A * z := by simp only [mul_assoc]
          _ = 1 := by rw [hz, mul_one, mul_assoc z A A, hA, mul_one, hz]
      apply evL_commW_of_pair _ (z * A * z) hzAz
      intro l
      cases l <;> simp only [liftL, killMap, Bool.false_eq_true, if_false, evL_cons, evL_nil,
        mul_one, lm_a, lm_b, lm_c, lm_d, lm_bcdGen, hy'] <;> try (left; rfl)
      all_goals (try split_ifs) <;> simp [hz, hz', mul_assoc]
    · apply evL_commW_of_pair _ A hA
      intro l
      cases l <;> simp only [liftL, killMap, if_true, evL_cons, evL_nil,
        mul_one, lm_a, lm_b, lm_c, lm_d, lm_bcdGen, hy', Bool.false_eq_true, if_false]
      · left; simp [hz]
      all_goals split_ifs <;> simp

/-! ### The words of Fact 7.6 -/

/-- A letter not killed by `i`. -/
def notKilled (i : Fin 3) : BCD := if i = 2 then .c else .b

theorem letterValue_notKilled (i : Fin 3) : letterValue i (notKilled i) = true := by
  revert i; decide

theorem letterValue_killedBy_of_ne (i j : Fin 3) (h : i ≠ j) :
    letterValue j (BCD.killedBy i) = true := by
  revert i j; decide

theorem letterValue_killedBy_self (i : Fin 3) : letterValue i (BCD.killedBy i) = false := by
  revert i; decide

theorem lm_grig_involutive (ω : ℕ → Fin 3) (k : ℕ) (l : Gen4) :
    lm grigA (gen (shiftSeq ω k)) l * lm grigA (gen (shiftSeq ω k)) l = 1 := by
  cases l <;> simp [grigA_mul_self, gen_mul_self]

theorem killMap_involutive (z A : BinaryTreeAut) (e : BCD → Bool) (hz : z * z = 1)
    (hA : A * A = 1) (l : Gen4) : killMap z A e l * killMap z A e l = 1 := by
  cases l <;> simp only [killMap, lm_a, lm_b, lm_c, lm_d] <;> try exact hz
  all_goals split_ifs <;> simp [hA]

theorem exists_word (ω : ℕ → Fin 3) (n : ℕ) (γ : BCD)
    (hγ : 1 ≤ n → letterValue (ω (n - 1)) γ = false) :
    ∀ (v : List Bool) (ℓ : ℕ), ℓ + v.length = n → ∃ w : List Gen4,
      evalWord ω ℓ w = iota ⁅gen (shiftSeq ω n) γ, grigA⁆ v ∧ w.length = 2 ^ (v.length + 2) ∧
      2 * w.count .a = w.length ∧ (∃ p q, w = commW p q) ∧
      (1 ≤ ℓ → Kill (letterValue (ω (ℓ - 1))) w) := by
  intro v
  induction v with
  | nil =>
    intro ℓ hℓ
    simp only [List.length_nil, Nat.add_zero] at hℓ
    subst hℓ
    refine ⟨commW [bcdGen γ] [.a], ?_, by simp [commW], ?_, ⟨_, _, rfl⟩, ?_⟩
    · rw [evalWord_eq_evL, evL_commW _ (lm_grig_involutive ω ℓ), iota_nil]
      simp [evL]
    · simp [commW, List.count_cons, bcdGen_ne_a]
    · intro hℓ z A hz hA
      rw [evL_commW _ (killMap_involutive z A _ hz hA)]
      simp [evL, killMap, hγ hℓ, commutatorElement_def]
  | cons x v ih =>
    intro ℓ hℓ
    simp only [List.length_cons] at hℓ
    obtain ⟨w', hev, hlen, hcount, ⟨p, q, hpq⟩, hkill⟩ := ih (ℓ + 1) (by omega)
    have hk : Kill (letterValue (ω ℓ)) w' := by simpa using hkill (by omega)
    obtain ⟨y, hy, hy'⟩ : ∃ y, letterValue (ω ℓ) y = true ∧
        (1 ≤ ℓ → letterValue (ω (ℓ - 1)) y = false ∨
          letterValue (ω (ℓ - 1)) = letterValue (ω ℓ)) := by
      by_cases h : ω (ℓ - 1) = ω ℓ
      · exact ⟨notKilled (ω ℓ), letterValue_notKilled _, fun _ => Or.inr (by rw [h])⟩
      · exact ⟨BCD.killedBy (ω (ℓ - 1)), letterValue_killedBy_of_ne _ _ h,
          fun _ => Or.inl (letterValue_killedBy_self _)⟩
    have hπ : evL (lm (gen (shiftSeq ω (ℓ + 1)) y) (letterElt (ω ℓ))) w' = 1 :=
      hk _ _ (gen_mul_self _ _) grigA_mul_self
    obtain ⟨hl1, hl2⟩ := lift_length x y w' hcount
    refine ⟨w'.flatMap (liftL x y), ?_, ?_, hl2, ?_, ?_⟩
    · cases x
      · rw [evalWord_lift_false ω ℓ y hy, hπ, hev, pairElt, iota_one, mul_one, iota_iota]
        rfl
      · rw [evalWord_lift_true ω ℓ y hy, hπ, hev, pairElt, iota_one, one_mul, iota_iota]
        rfl
    · rw [hl1, hlen, List.length_cons, pow_succ]; ring
    · exact ⟨_, _, hpq ▸ lift_commW x y p q⟩
    · intro hℓ1
      rw [hpq]
      apply kill_lift (letterValue (ω ℓ)) _ x y p q
      rcases hy' hℓ1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hpq ▸ hk⟩

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

theorem frI_sep (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) {a b : ℕ} (ha : a ∈ frI D ω)
    (hb : b ∈ frI D ω) (hab : a < b) : a + 3 ≤ b := by
  obtain ⟨ℓ1, rfl⟩ := ha
  obtain ⟨ℓ2, rfl⟩ := hb
  have h1 := (frM_spec D ω hω ℓ1).1
  have h2 := (frM_spec D ω hω ℓ2).1
  rcases Nat.lt_trichotomy ℓ1 ℓ2 with h | rfl | h
  · have : (ℓ1 + 1) * D ≤ ℓ2 * D := Nat.mul_le_mul_right D h
    have : (ℓ1 + 1) * D = ℓ1 * D + D := by ring
    omega
  · omega
  · have : (ℓ2 + 1) * D ≤ ℓ1 * D := Nat.mul_le_mul_right D h
    have : (ℓ2 + 1) * D = ℓ2 * D + D := by ring
    omega

theorem window_of_mem_frI (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) {s : ℕ}
    (hs : s ∈ frI D ω) :
    3 ≤ s ∧ ω (s - 3) = 2 ∧ (ω (s - 2) = 0 ∨ ω (s - 2) = 1) ∧ ω (s - 1) = 1 := by
  obtain ⟨ℓ, rfl⟩ := hs
  obtain ⟨-, h2, h3, h4⟩ := frM_spec D ω hω ℓ
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [show ℓ * D + frM D ω ℓ + 3 - 3 = ℓ * D + frM D ω ℓ by omega]; exact h2
  · rw [show ℓ * D + frM D ω ℓ + 3 - 2 = ℓ * D + frM D ω ℓ + 1 by omega]; exact h4
  · rw [show ℓ * D + frM D ω ℓ + 3 - 1 = ℓ * D + frM D ω ℓ + 2 by omega]; exact h3

theorem getElem_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ)
    (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = false) : D - j % D ≤ t ∧ j + (t + 1) ∈ frI D ω := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  have hjj : j % D ≤ j := Nat.mod_le _ _
  obtain ⟨u, ⟨hu, hu2⟩, rfl⟩ := hv
  simp only [List.append_assoc] at ht hf
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at ht
  by_cases h1 : t < D - j % D
  · rw [List.getElem_append_left (by simp; omega)] at hf
    simp at hf
  push Not at h1
  rw [List.getElem_append_right (by simp; omega)] at hf
  simp only [List.length_replicate] at hf
  by_cases h2 : t - (D - j % D) < k
  · rw [List.getElem_append_left (by simp [hu]; omega)] at hf
    refine ⟨h1, ?_⟩
    by_contra hnot
    have := hu2 (t - (D - j % D)) (by rw [hu]; exact h2)
      (by
        have e : j + D - j % D + (t - (D - j % D) + 1) = j + (t + 1) := by omega
        rw [e]; exact hnot)
    rw [this] at hf
    exact Bool.noConfusion hf
  push Not at h2
  rw [List.getElem_append_right (by simp [hu]; omega)] at hf
  simp only [hu] at hf
  by_cases h3 : t - (D - j % D) - k < frM D ω (ellIndex D k j) + 2
  · rw [List.getElem_append_left (by simp; omega)] at hf
    simp at hf
  refine ⟨h1, ⟨ellIndex D k j, ?_⟩⟩
  have hlast : t = D - j % D + k + frM D ω (ellIndex D k j) + 2 := by omega
  have hdiv : D ∣ j + D - j % D + k := by
    have h1 : j + D - j % D = D * (j / D) + D := by
      have := Nat.div_add_mod j D
      omega
    rw [h1]
    exact Dvd.dvd.add (Dvd.dvd.add (Dvd.intro _ rfl) (dvd_refl D)) hk
  have hell : ellIndex D k j * D = j + D - j % D + k := by
    unfold ellIndex
    exact Nat.div_mul_cancel hdiv
  rw [hell, hlast]
  omega

/-! ### `[b, a]` below `1` -/

theorem dec_comm_b (ω : ℕ → Fin 3) (hb : letterValue (ω 0) .b = true) :
    Dec3 ⁅gen ω .b, grigA⁆ false (grigA * gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .b * grigA) := by
  have hg : Dec3 (gen ω .b) false grigA (gen (shiftSeq ω 1) .b) := by
    refine ⟨rootSwap_gen _ _, ?_, sec_gen_true _ _⟩
    rw [sec_gen_false]; simp [letterElt, hb]
  rw [commutatorElement_def, gen_inv, grigA_inv]
  have := dec_mul (dec_mul (dec_mul hg dec_grigA) hg) dec_grigA
  simpa [mul_assoc] using this

/-! ### The milestone -/

theorem hElt_of_false (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = false) :
    hElt ω j v (t + 1) = iota ⁅gen (shiftSeq ω (j + (t + 1) - 2)) .b, grigA⁆ (v.take (t + 1 - 2)) := by
  have : v.getD (t + 1 - 1) true = false := by
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ ht, hf]
  unfold hElt
  rw [this]
  simp

theorem hElt_of_true (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (t : ℕ) (ht : t < v.length)
    (hf : v[t] = true) : hElt ω j v (t + 1) = 1 := by
  have : v.getD (t + 1 - 1) true = true := by
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ ht, hf]
  unfold hElt
  rw [this]
  simp

end ConstrH

end ErschlerZheng
end

section
/-!
# Lemma 7.9 (corrected) and its printed failure (Erschler–Zheng p. 39)

`a𝔠^v_j = a H⁻¹ c H` is the value of the explicit even-length word `a U^R c U` (`U` a word for
`H = h^v_1 ⋯ h^v_{k'}`, from Fact 7.6), hence of a free-group word `w` over `{ab, ac, ad}`
(pair the letters: `x y = (a x)⁻¹ (a y)`). The parity character `χ_κ` (number of `aκ` letters
mod 2) satisfies `χ_κ ∘ ζ_i = χ_{κ_i}` (`κ_i` the letter killed by `i`), and the root swap of
`ζ_i(u)` evaluated is `χ_{κ_i}(u)` (A5). So every stage of `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}(w)`
has root swap `χ_{κ_{j-1}}(w)`: `0` when `ω_{j-1} ≠ 1` (even numbers of `b` and `d`), `1` when
`ω_{j-1} = 1` (odd number of `c`). With (2.3) this gives Lemma 7.9 and its failure.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrG

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH

/-! ### Words for `hProd` and `a𝔠` -/

theorem evalWord_shift_zero (ω : ℕ → Fin 3) (j : ℕ) (u : List Gen4) :
    evalWord (shiftSeq ω j) 0 u = evalWord ω j u := by
  rw [evalWord_eq_evL, evalWord_eq_evL, shiftSeq_zero]

theorem exists_word_prod (ω : ℕ → Fin 3) (j : ℕ) (l : List BinaryTreeAut)
    (hl : ∀ x ∈ l, ∃ u, evalWord ω j u = x) : ∃ U, evalWord ω j U = l.prod := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    obtain ⟨u, hu⟩ := hl x (by simp)
    obtain ⟨U, hU⟩ := ih (fun y hy => hl y (by simp [hy]))
    exact ⟨u ++ U, by rw [evalWord_append, hu, hU, List.prod_cons]⟩

theorem exists_word_hProd (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) : ∃ U, evalWord ω j U = hProd ω j v := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  apply exists_word_prod
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have ht' : t < v.length := List.mem_range.mp ht
  cases hvt : v[t]
  · obtain ⟨h1, hI⟩ := getElem_of_mem_vSet D ω hω j k hk v hv t ht' hvt
    have ht1 : 1 ≤ t := by have := Nat.mod_lt j (show 0 < D by omega); omega
    obtain ⟨-, w1, -, -⟩ := window_of_mem_frI D ω hω hI
    obtain ⟨u, hu, -⟩ := exists_word (shiftSeq ω j) (t + 1 - 2) .b
      (by
        intro _
        simp only [shiftSeq]
        rw [show t + 1 - 2 - 1 + j = j + (t + 1) - 3 by omega, w1]
        decide)
      (v.take (t + 1 - 2)) 0 (by simp; omega)
    refine ⟨u, ?_⟩
    rw [← evalWord_shift_zero, hu, hElt_of_false ω j v t ht' hvt]
    rw [shiftSeq_shiftSeq, show t + 1 - 2 + j = j + (t + 1) - 2 by omega]
  · exact ⟨[], by rw [hElt_of_true ω j v t ht' hvt]; rfl⟩

theorem evalWord_reverse (ω : ℕ → Fin 3) (j : ℕ) (U : List Gen4) :
    evalWord ω j U.reverse = (evalWord ω j U)⁻¹ := by
  rw [evalWord_eq_evL, evalWord_eq_evL, evL_reverse _ (lm_grig_involutive ω j)]

/-- The word `a U^R c U` for `a𝔠^v_j`. -/
def acWord (U : List Gen4) : List Gen4 := [.a] ++ U.reverse ++ [.c] ++ U

theorem evalWord_acWord (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (U : List Gen4)
    (hU : evalWord ω j U = hProd ω j v) :
    evalWord ω j (acWord U) = grigA * cElt ω j v := by
  unfold acWord cElt
  rw [evalWord_append, evalWord_append, evalWord_append, evalWord_reverse, hU]
  simp [evalWord, mul_assoc]

/-! ### Free-group words from even-length words -/

/-- The free-group element with value `a x`. -/
def lt : Gen4 → FreeGroup APair
  | .a => 1
  | .b => .of .ab
  | .c => .of .ac
  | .d => .of .ad

/-- Pair the letters: `x y ↦ (a x)⁻¹ (a y)`. -/
def conv : List Gen4 → FreeGroup APair
  | x :: y :: rest => (lt x)⁻¹ * lt y * conv rest
  | _ => 1

theorem evalFree_lt (ω : ℕ → Fin 3) (k : ℕ) (x : Gen4) :
    evalFree ω k (lt x) = grigA * lm grigA (gen (shiftSeq ω k)) x := by
  cases x
  · simp [lt, grigA_mul_self]
  all_goals simp [lt, evalFree_of, evalWord_toWord, pairLetter]

theorem evalFree_conv (ω : ℕ → Fin 3) (k : ℕ) :
    ∀ n (w : List Gen4), w.length = 2 * n → evalFree ω k (conv w) = evalWord ω k w := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst this; rfl
  | succ n ih =>
    intro w hw
    match w, hw with
    | x :: y :: rest, hw =>
      simp only [List.length_cons] at hw
      rw [conv, map_mul, map_mul, map_inv, ih rest (by omega), evalFree_lt, evalFree_lt,
        evalWord_eq_evL, evalWord_eq_evL, evL_cons, evL_cons, mul_inv_rev, grigA_inv]
      have hx := lm_grig_involutive ω k x
      have hxi : (lm grigA (gen (shiftSeq ω k)) x)⁻¹ = lm grigA (gen (shiftSeq ω k)) x :=
        inv_eq_of_mul_eq_one_right hx
      rw [hxi]
      simp only [mul_assoc, grigA_mul_grigA_mul]

/-- The parity of the number of letters `aκ`. -/
def chi (κ : BCD) : FreeGroup APair →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun p => Multiplicative.ofAdd (if pairLetter p = κ then 1 else 0)

theorem chi_lt (κ : BCD) (x : Gen4) :
    chi κ (lt x) = Multiplicative.ofAdd (if x = bcdGen κ then 1 else 0) := by
  cases x <;> cases κ <;> simp [lt, chi, pairLetter, bcdGen] <;> rfl

theorem chi_conv (κ : BCD) :
    ∀ n (w : List Gen4), w.length = 2 * n →
      chi κ (conv w) = Multiplicative.ofAdd ((w.count (bcdGen κ) : ℕ) : ZMod 2) := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst this; rfl
  | succ n ih =>
    intro w hw
    match w, hw with
    | x :: y :: rest, hw =>
      simp only [List.length_cons] at hw
      rw [conv, map_mul, map_mul, map_inv, ih rest (by omega), chi_lt, chi_lt,
        List.count_cons, List.count_cons]
      rw [← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
      congr 1
      have hneg : ∀ z : ZMod 2, -z = z := by decide
      rw [hneg]
      split_ifs <;> simp_all <;> push_cast <;> ring

/-! ### The parity character and the substitutions -/

/-- The root-swap bit as a homomorphism. -/
def bitHom : BinaryTreeAut →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (bit g)
  map_one' := by simp [bit_one]
  map_mul' g h := by simp [bit_mul, ofAdd_add]

theorem bit_evalFree_zetaFree (ω : ℕ → Fin 3) (m : ℕ) (u : FreeGroup APair) :
    Multiplicative.ofAdd (bit (evalFree ω m (zetaFree (ω m) u))) =
      chi (BCD.killedBy (ω m)) u := by
  have : bitHom.comp ((evalFree ω m).comp (zetaFree (ω m))) = chi (BCD.killedBy (ω m)) := by
    apply FreeGroup.ext_hom
    intro p
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    show Multiplicative.ofAdd (bit (evalFree ω m (zetaFree (ω m) (FreeGroup.of p)))) = _
    rw [bit_evalFree_zetaFree_of]
    simp [chi]
  exact DFunLike.congr_fun this u

theorem chi_zetaFree (κ : BCD) (i : Fin 3) (u : FreeGroup APair) :
    chi κ (zetaFree i u) = chi (BCD.killedBy i) u := by
  have : (chi κ).comp (zetaFree i) = chi (BCD.killedBy i) := by
    apply FreeGroup.ext_hom
    intro p
    simp only [MonoidHom.coe_comp, Function.comp_apply, zetaFree, FreeGroup.lift_apply_of]
    rcases fin3_cases i with rfl | rfl | rfl <;> cases p <;> cases κ <;>
      simp [zetaPair, chi, pairLetter, BCD.killedBy, ← ofAdd_add] <;> decide
  exact DFunLike.congr_fun this u

/-- `ζ_{ω_m} ∘ ⋯ ∘ ζ_{ω_{m+r-1}}`. -/
def zfold (ω : ℕ → Fin 3) : ℕ → ℕ → FreeGroup APair → FreeGroup APair
  | _, 0, w => w
  | m, r + 1, w => zetaFree (ω m) (zfold ω (m + 1) r w)

theorem foldr_range'_eq (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    ∀ r m, (List.range' m r).foldr (fun k w => zetaFree (ω k) w) w = zfold ω m r w := by
  intro r
  induction r with
  | zero => intro m; rfl
  | succ r ih => intro m; rw [List.range'_succ, List.foldr_cons, ih]; rfl

theorem chi_zfold (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    ∀ r m κ, chi κ (zfold ω m (r + 1) w) = chi (BCD.killedBy (ω (m + r))) w := by
  intro r
  induction r with
  | zero => intro m κ; simp [zfold, chi_zetaFree]
  | succ r ih =>
    intro m κ
    rw [zfold, chi_zetaFree, ih (m + 1), show m + 1 + r = m + (r + 1) by omega]

/-- The bit of every stage. -/
theorem bit_zfold (ω : ℕ → Fin 3) (w : FreeGroup APair) (r m : ℕ) :
    Multiplicative.ofAdd (bit (evalFree ω m (zfold ω m (r + 1) w))) =
      chi (BCD.killedBy (ω (m + r))) w := by
  rw [zfold, bit_evalFree_zetaFree]
  cases r with
  | zero => rfl
  | succ r => rw [chi_zfold, show m + 1 + r = m + (r + 1) by omega]

theorem rootSwap_eq_of_bit {g : BinaryTreeAut} (h : Multiplicative.ofAdd (bit g) = 1) :
    rootSwap g = false := by
  unfold bit at h
  cases hg : rootSwap g
  · rfl
  · rw [hg] at h; exact absurd h (by decide)

/-! ### The structure of `g̃` -/

/-! ### The free word for `a𝔠` and the tail condition -/

theorem tail_of_fr (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ) (i : Fin 3) :
    ∃ m, k < m ∧ ω m ≠ i := by
  obtain ⟨m, hm, h2, h1, -⟩ := hω (k + 1)
  have hD : 1 ≤ D := by omega
  have : k + 1 ≤ (k + 1) * D := Nat.le_mul_of_pos_right _ hD
  by_cases hi : i = 2
  · exact ⟨(k + 1) * D + m + 2, by omega, by rw [h1, hi]; decide⟩
  · exact ⟨(k + 1) * D + m, by omega, by rw [h2]; exact Ne.symm hi⟩

theorem ofAdd_two (x : ZMod 2) : Multiplicative.ofAdd x * Multiplicative.ofAdd x = 1 := by
  rw [← ofAdd_add]
  have : x + x = 0 := by fin_cases x <;> decide
  rw [this]; rfl

theorem exists_free_word (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) :
    ∃ w : FreeGroup APair, evalFree ω j w = grigA * cElt ω j v ∧
      chi .b w = 1 ∧ chi .d w = 1 ∧ chi .c w = Multiplicative.ofAdd 1 := by
  obtain ⟨U, hU⟩ := exists_word_hProd D ω hω j k hk v hv
  have hlen : (acWord U).length = 2 * (U.length + 1) := by simp [acWord]; ring
  refine ⟨conv (acWord U), ?_, ?_, ?_, ?_⟩
  · rw [evalFree_conv ω j _ _ hlen, evalWord_acWord ω j v U hU]
  all_goals
    rw [chi_conv _ _ _ hlen]
    simp only [acWord, List.count_append, List.count_reverse, List.count_cons, List.count_nil,
      bcdGen]
    simp
  · exact ofAdd_two _
  · exact ofAdd_two _
  · rw [mul_comm (Multiplicative.ofAdd _) (Multiplicative.ofAdd 1), mul_assoc, ofAdd_two,
      mul_one]

theorem gTilde_eq (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj : 1 ≤ j)
    (v : List Bool) (w : FreeGroup APair) (hw : evalFree ω j w = grigA * cElt ω j v) :
    gTilde ω j v = evalFree ω 0 (zfold ω 0 j w) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have := (evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne ω n
    (fun i _ => tail_of_fr D ω hω n i)).2.2.2 0 (Nat.zero_le n)
      (fun k _ _ i _ => tail_of_fr D ω hω k i) w
  rw [List.Ico.zero_bot] at this
  unfold gTilde
  rw [← hw, this, List.range_eq_range', foldr_range'_eq]

/-! ### The printed claim fails at `ω = (201)^∞`, `D = 3`, `j = 3`, `k = 3` -/

end ConstrG

end ErschlerZheng
end

section
/-!
# The sequence `g_n` of (7.1) (Erschler–Zheng p. 35)

`g_n = ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{n-1}}(aγ)` with `γ = c` if `ω_{n-1} = 2`, else `b`: the letter `aγ`
has `χ_{κ_{n-1}} = 0`, so every substitution stage fixes level 1 (`ConstrG`), `g_n ∈ St(L_n)` with
sections `aγ` or `γa` at level `n`; cube independence is Lemma 5.6 (A13b); the germs are read from
the sections at level `n + 1`, which lie in `{1, a, γ_{𝔰^{n+1}ω}}`, with B4 (for `⟨c⟩`, B4 applied to
the string with the letters `1` and `2` exchanged, whose `b` is `c_ω`).
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrSeq

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG

/-! ### `g_n` as a substituted free-group word -/

theorem zetaFree_prod_map_of (i : Fin 3) (l : List APair) :
    zetaFree i (l.map FreeGroup.of).prod = ((zetaWord i l).map FreeGroup.of).prod := by
  induction l with
  | nil => simp [zetaWord]
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih]
    simp [zetaWord, zetaFree, List.flatMap_cons, List.map_append, List.prod_append]

theorem foldr_zetaWord_eq (ω : ℕ → Fin 3) (l : List APair) :
    ∀ r m, (((List.range' m r).foldr (fun i w => zetaWord (ω i) w) l).map FreeGroup.of).prod =
      zfold ω m r (l.map FreeGroup.of).prod := by
  intro r
  induction r with
  | zero => intro m; rfl
  | succ r ih =>
    intro m
    rw [List.range'_succ, List.foldr_cons, ← zetaFree_prod_map_of, ih]
    rfl

/-- The pair `aγ` of (7.1). -/
def seqPair (ω : ℕ → Fin 3) (n : ℕ) : APair := if ω (n - 1) = 2 then .ac else .ab

theorem seqG_eq (ω : ℕ → Fin 3) (n : ℕ) :
    seqG ω n = evalFree ω 0 (zfold ω 0 n (FreeGroup.of (seqPair ω n))) := by
  unfold seqG
  rw [← evalFree_prod_map_of, List.range_eq_range', foldr_zetaWord_eq]
  simp [seqPair]

/-! ### Exchanging the letters `1` and `2` -/

/-! ### Generators that differ -/

/-! ### The milestone -/

end ConstrSeq

end ErschlerZheng
end

section
/-!
# Lemma 7.7: the sections of `𝔠^v_j` along the path `v` (Erschler–Zheng p. 38)

For a string `ω` and a word `v`, `kProd ω v = k_1 ⋯ k_{|v|}` with `k_i = 1` if `v_i = 1`,
`k_1 = a` if `v_1 = 0`, and `k_i = ι([b_{𝔰^{i-2}ω}, a], v_1 … v_{i-2})` if `v_i = 0`, `i ⩾ 2`;
`qElt ω v = kProd⁻¹ c_ω kProd`. When `v_1 = 1`, `hProd ω j v = kProd (𝔰^j ω) v` and
`cElt ω j v = qElt (𝔰^j ω) v`. One level down:
`qElt ω (1 :: v') = (s, qElt (𝔰ω) v')` and `qElt ω (0 :: v') = (qElt (𝔰ω) v', ω_0(c))`, where
`s = b a ω_0(c) a b` (`b = b_{𝔰ω}`) if `v'` starts with `0`, and `s = ω_0(c)` otherwise.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrC

open GrigBasic ZetaDev ConstrW ConstrIota ConstrH

/-- `k_i`. -/
def kElt (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) : BinaryTreeAut :=
  if v.getD (i - 1) true then 1
  else if i = 1 then grigA else iota ⁅gen (shiftSeq ω (i - 2)) .b, grigA⁆ (v.take (i - 2))

/-- `k_1 ⋯ k_{|v|}`. -/
def kProd (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  ((List.range v.length).map fun i => kElt ω v (i + 1)).prod

/-- `k_2 ⋯ k_{|v|}`. -/
def tailProd (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  ((List.range (v.length - 1)).map fun i => kElt ω v (i + 2)).prod

/-- `kProd⁻¹ c_ω kProd`. -/
def qElt (ω : ℕ → Fin 3) (v : List Bool) : BinaryTreeAut :=
  (kProd ω v)⁻¹ * gen ω .c * kProd ω v

theorem kProd_eq (ω : ℕ → Fin 3) (v : List Bool) : kProd ω v = kElt ω v 1 * tailProd ω v := by
  unfold kProd tailProd
  cases v with
  | nil => simp [kElt]
  | cons x v' =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def]

theorem iota_list_prod (l : List BinaryTreeAut) (u : List Bool) :
    iota l.prod u = (l.map fun g => iota g u).prod := by
  induction l with
  | nil => simp [iota_one]
  | cons g l ih => rw [List.prod_cons, ← iota_mul, ih, List.map_cons, List.prod_cons]

theorem kElt_cons_add_three (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) (i : ℕ) :
    kElt ω (x :: v') (i + 3) = iota (kElt (shiftSeq ω 1) v' (i + 2)) [x] := by
  unfold kElt
  have h1 : (x :: v').getD (i + 3 - 1) true = v'.getD (i + 2 - 1) true := by
    simp
  rw [h1, if_neg (show i + 3 ≠ 1 by omega), if_neg (show i + 2 ≠ 1 by omega)]
  split_ifs with h
  · rw [iota_one]
  · have e1 : shiftSeq ω (i + 3 - 2) = shiftSeq (shiftSeq ω 1) (i + 2 - 2) := by
      rw [shiftSeq_shiftSeq]; congr 1
    rw [e1, iota_iota]
    congr 1

theorem tailProd_cons (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) :
    tailProd ω (x :: v') = kElt ω (x :: v') 2 * iota (tailProd (shiftSeq ω 1) v') [x] := by
  unfold tailProd
  cases v' with
  | nil => simp [kElt, iota_one]
  | cons y v'' =>
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, iota_list_prod]
    congr 1
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    exact kElt_cons_add_three ω x (y :: v'') i

theorem kElt_one (ω : ℕ → Fin 3) (v : List Bool) :
    kElt ω v 1 = if v.head? = some false then grigA else 1 := by
  unfold kElt
  cases v with
  | nil => simp
  | cons x v => cases x <;> simp

theorem kElt_two (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) :
    kElt ω (x :: v') 2 = if v'.head? = some false then ⁅gen ω .b, grigA⁆ else 1 := by
  unfold kElt
  cases v' with
  | nil => simp
  | cons y v'' => cases y <;> simp [iota_nil, shiftSeq_zero]

theorem pairElt_inv (g h : BinaryTreeAut) : (pairElt g h)⁻¹ = pairElt g⁻¹ h⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [pairElt_mul, mul_inv_cancel, mul_inv_cancel, pairElt_one]

theorem iota_true_eq (g : BinaryTreeAut) : iota g [true] = pairElt 1 g := by
  simp [pairElt, iota_one]

theorem iota_false_eq (g : BinaryTreeAut) : iota g [false] = pairElt g 1 := by
  simp [pairElt, iota_one]

theorem gen_c_eq (ω : ℕ → Fin 3) :
    gen ω .c = pairElt (letterElt (ω 0) .c) (gen (shiftSeq ω 1) .c) := by
  have := gen_eq_pairElt ω 0 .c
  simpa [shiftSeq_zero] using this

theorem comm_b_eq (ω : ℕ → Fin 3) (hb : letterValue (ω 0) .b = true) :
    ⁅gen ω .b, grigA⁆ = pairElt (grigA * gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .b * grigA) :=
  eq_of_dec (dec_comm_b ω hb) (dec_pairElt _ _)

theorem b_conj_c (ω : ℕ → Fin 3) : gen ω .b * gen ω .c * gen ω .b = gen ω .c := by
  rw [gen_b_mul_c, gen_d_mul_b]

/-- The section off the path at depth `i + 1`. -/
def sSib (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) : BinaryTreeAut :=
  if v.getD i true = true ∧ v.getD (i + 1) true = false then
    gen (shiftSeq ω (i + 1)) .b * grigA * letterElt (ω i) .c * grigA * gen (shiftSeq ω (i + 1)) .b
  else letterElt (ω i) .c

theorem pairElt_conj (g h e c : BinaryTreeAut) :
    (pairElt g h)⁻¹ * pairElt e c * pairElt g h = pairElt (g⁻¹ * e * g) (h⁻¹ * c * h) := by
  rw [pairElt_inv, pairElt_mul, pairElt_mul]

theorem conj_mul (g P C : BinaryTreeAut) : (g * P)⁻¹ * C * (g * P) = P⁻¹ * (g⁻¹ * C * g) * P := by
  group

/-- One level down. -/
theorem qElt_cons (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool)
    (h1 : x = false → v'.head? ≠ some false)
    (h2 : x = true → v'.head? = some false → letterValue (ω 0) .b = true) :
    qElt ω (x :: v') = if x then pairElt (sSib ω (x :: v') 0) (qElt (shiftSeq ω 1) v')
      else pairElt (qElt (shiftSeq ω 1) v') (letterElt (ω 0) .c) := by
  have hk := kProd_eq ω (x :: v')
  have hk' := kProd_eq (shiftSeq ω 1) v'
  rw [tailProd_cons, ← mul_assoc] at hk
  unfold qElt
  rw [hk, hk', gen_c_eq ω, kElt_one, kElt_two, kElt_one]
  generalize tailProd (shiftSeq ω 1) v' = T
  cases x
  · have hh : v'.head? ≠ some false := h1 rfl
    have e1 : (if (false :: v').head? = some false then grigA else 1) = grigA := by simp
    rw [e1, if_neg hh, if_neg hh, mul_one, one_mul, iota_false_eq, conj_mul, grigA_inv,
      grigA_conj_pairElt, pairElt_conj]
    simp
  · have e1 : (if (true :: v').head? = some false then grigA else 1) = 1 := by simp
    rw [e1, one_mul, if_pos rfl]
    by_cases hh : v'.head? = some false
    · have hb := h2 rfl hh
      rw [if_pos hh, if_pos hh, comm_b_eq ω hb, iota_true_eq, pairElt_mul, pairElt_conj]
      have hv0 : v'.getD 0 true = false := by
        cases v' with
        | nil => simp at hh
        | cons y v'' => simp at hh; simp [hh]
      congr 1
      · simp only [sSib, List.getD_cons_zero, List.getD_cons_succ, hv0, and_self, if_true,
          Nat.zero_add, mul_one, mul_inv_rev, gen_inv, grigA_inv, mul_assoc]
      · simp only [mul_inv_rev, gen_inv, grigA_inv, mul_assoc]
        rw [← mul_assoc (gen (shiftSeq ω 1) .b) (gen (shiftSeq ω 1) .c),
          ← mul_assoc (gen (shiftSeq ω 1) .b * gen (shiftSeq ω 1) .c), b_conj_c]
    · rw [if_neg hh, if_neg hh]
      simp only [one_mul, mul_one]
      rw [iota_true_eq, pairElt_conj]
      have hv0 : ¬ (v'[0]?.getD true = false) := by
        cases v' with
        | nil => simp
        | cons y v'' => cases y <;> simp_all
      simp only [sSib, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, if_neg (by simp [hv0])]
      simp

/-! ### The milestone -/

theorem hProd_eq_kProd (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (hv : v.getD 0 true = true) :
    hProd ω j v = kProd (shiftSeq ω j) v := by
  unfold hProd kProd
  congr 1
  apply List.map_congr_left
  intro i _
  unfold hElt kElt
  simp only [Nat.add_sub_cancel]
  split_ifs with h1 h2
  · rfl
  · have : i = 0 := by omega
    subst this
    exact absurd hv h1
  · rw [shiftSeq_shiftSeq, show j + (i + 1) - 2 = i + 1 - 2 + j by omega]

theorem cElt_eq_qElt (ω : ℕ → Fin 3) (j : ℕ) (v : List Bool) (hv : v.getD 0 true = true) :
    cElt ω j v = qElt (shiftSeq ω j) v := by
  unfold cElt qElt
  rw [hProd_eq_kProd ω j v hv]

end ConstrC

end ErschlerZheng
end

section
/-!
# Fact 7.14: on level `n + D + 1`, every element of `𝔉_{j,n}` acts as `g_j` (p. 44)

`g̃^v_j` and `g_j` are `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}` of `a𝔠^v_j` and `ac_{𝔰^jω}`; both fix level `j`, and
at each vertex of level `j` their sections are `(a𝔠, ac)` or `(𝔠a, ca)` (`goodPair_zfold`). If `v`
begins with `1^p`, then `𝔠^v_j = qElt (𝔰^jω) v` and `c = qElt (𝔰^jω) 1^{|v|}` agree on level `p + 1`
(`qElt_agree`, one level at a time with `qElt_cons`); here `p = n - j + D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrFact714

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC

/-- No two consecutive zeros. -/
def H1 (v : List Bool) : Prop := ∀ i (h : i + 1 < v.length), v[i] = false → v[i + 1] = true

/-- `b` is not killed just before a zero. -/
def H2 (ω : ℕ → Fin 3) (v : List Bool) : Prop :=
  ∀ i (h : i + 1 < v.length), v[i + 1] = false → letterValue (ω i) .b = true

theorem vSet_props (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j k : ℕ) (hk : D ∣ k)
    (v : List Bool) (hv : v ∈ vSet D ω j k) :
    v.getD 0 true = true ∧ H1 v ∧ H2 (shiftSeq ω j) v := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hzero : ∀ t (ht : t < v.length), v[t] = false → j + (t + 1) ∈ frI D ω :=
    fun t ht hf => (getElem_of_mem_vSet D ω hω j k hk v hv t ht hf).2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, -, rfl⟩ := hv
    have : 0 < D - j % D := by have := Nat.mod_lt j (show 0 < D by omega); omega
    obtain ⟨m, hm⟩ : ∃ m, D - j % D = m + 1 := ⟨D - j % D - 1, by omega⟩
    rw [hm]
    simp [List.replicate_succ]
  · intro i h hf
    by_contra hne
    have hf' : v[i + 1] = false := by simpa using hne
    have := frI_sep D ω hω (hzero i (by omega) hf) (hzero (i + 1) h hf') (by omega)
    omega
  · intro i h hf
    obtain ⟨-, -, hw, -⟩ := window_of_mem_frI D ω hω (hzero (i + 1) h hf)
    rw [show j + (i + 1 + 1) - 2 = j + i by omega] at hw
    simp only [shiftSeq]
    rw [Nat.add_comm i j]
    rcases hw with hw | hw <;> rw [hw] <;> decide

theorem H1_tail {x : Bool} {v' : List Bool} (h : H1 (x :: v')) : H1 v' :=
  fun i hi hf => h (i + 1) (by simp; omega) hf

theorem H2_tail {ω : ℕ → Fin 3} {x : Bool} {v' : List Bool} (h : H2 ω (x :: v')) :
    H2 (shiftSeq ω 1) v' :=
  fun i hi hf => h (i + 1) (by simp; omega) hf

theorem qElt_cons' (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) (h1 : H1 (x :: v'))
    (h2 : H2 ω (x :: v')) :
    qElt ω (x :: v') = if x then pairElt (sSib ω (x :: v') 0) (qElt (shiftSeq ω 1) v')
      else pairElt (qElt (shiftSeq ω 1) v') (letterElt (ω 0) .c) :=
  qElt_cons ω x v'
    (by
      rintro rfl hh
      cases v' with
      | nil => simp at hh
      | cons y v'' =>
        simp at hh
        have := h1 0 (by simp) rfl
        simp [hh] at this)
    (by
      rintro rfl hh
      cases v' with
      | nil => simp at hh
      | cons y v'' =>
        simp at hh
        exact h2 0 (by simp) (by simp [hh]))

theorem rootSwap_qElt (ω : ℕ → Fin 3) (v : List Bool) : rootSwap (qElt ω v) = false := by
  unfold qElt
  rw [rootSwap_mul, rootSwap_mul, rootSwap_inv, rootSwap_gen]
  cases rootSwap (kProd ω v) <;> rfl

theorem rootSwap_sSib (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) :
    rootSwap (sSib ω v i) = rootSwap (letterElt (ω i) .c) := by
  unfold sSib
  split_ifs
  · simp only [rootSwap_mul, rootSwap_gen, rootSwap_grigA]
    cases rootSwap (letterElt (ω i) .c) <;> rfl
  · rfl

theorem singleton_smul_eq_of_rootSwap {g h : BinaryTreeAut} (hgh : rootSwap g = rootSwap h)
    (z : List Bool) (hz : z.length = 1) : z <• g = z <• h := by
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hz
  rw [singleton_smul, singleton_smul, hgh]

/-- Two path elements whose words share a prefix of length `p` agree on level `p + 1`. -/
theorem qElt_agree : ∀ (p : ℕ) (ω : ℕ → Fin 3) (v1 v2 : List Bool), H1 v1 → H2 ω v1 → H1 v2 →
    H2 ω v2 → p ≤ v1.length → p ≤ v2.length → v1.take p = v2.take p →
    ∀ z : List Bool, z.length = p + 1 → z <• qElt ω v1 = z <• qElt ω v2 := by
  intro p
  induction p with
  | zero =>
    intro ω v1 v2 _ _ _ _ _ _ _ z hz
    exact singleton_smul_eq_of_rootSwap ((rootSwap_qElt ω v1).trans (rootSwap_qElt ω v2).symm) z
      hz
  | succ p ih =>
    intro ω v1 v2 a1 a2 b1 b2 l1 l2 ht z hz
    obtain ⟨x, v1', rfl⟩ : ∃ x v1', v1 = x :: v1' := by
      cases v1 with
      | nil => simp at l1
      | cons x v1' => exact ⟨x, v1', rfl⟩
    obtain ⟨x', v2', rfl⟩ : ∃ x v2', v2 = x :: v2' := by
      cases v2 with
      | nil => simp at l2
      | cons x v2' => exact ⟨x, v2', rfl⟩
    simp only [List.take_succ_cons, List.cons.injEq] at ht
    obtain ⟨rfl, ht'⟩ := ht
    obtain ⟨y, z', rfl⟩ : ∃ y z', z = y :: z' := by
      cases z with
      | nil => simp at hz
      | cons y z' => exact ⟨y, z', rfl⟩
    have hz' : z'.length = p + 1 := by simpa using hz
    rw [cons_smul, cons_smul, rootSwap_qElt, rootSwap_qElt, qElt_cons' ω x v1' a1 a2,
      qElt_cons' ω x v2' b1 b2]
    congr 1
    by_cases hyx : y = x
    · subst hyx
      cases y
      · simp only [Bool.false_eq_true, if_false, (dec_pairElt _ _).2.1]
        exact ih _ _ _ (H1_tail a1) (H2_tail a2) (H1_tail b1) (H2_tail b2)
          (by simp at l1; omega) (by simp at l2; omega) ht' z' hz'
      · simp only [if_true, (dec_pairElt _ _).2.2]
        exact ih _ _ _ (H1_tail a1) (H2_tail a2) (H1_tail b1) (H2_tail b2)
          (by simp at l1; omega) (by simp at l2; omega) ht' z' hz'
    · cases x <;> cases y <;> simp only [Bool.false_eq_true, if_false, if_true] at hyx ⊢
      · simp at hyx
      · rw [(dec_pairElt _ _).2.2, (dec_pairElt _ _).2.2]
      · rw [(dec_pairElt _ _).2.1, (dec_pairElt _ _).2.1]
        cases p with
        | zero =>
          exact singleton_smul_eq_of_rootSwap
            ((rootSwap_sSib _ _ _).trans (rootSwap_sSib _ _ _).symm) z' hz'
        | succ p =>
          have hs : sSib ω (true :: v1') 0 = sSib ω (true :: v2') 0 := by
            unfold sSib
            have : v1'.getD 0 true = v2'.getD 0 true := by
              cases v1' with
              | nil => simp at l1
              | cons a v1'' =>
                cases v2' with
                | nil => simp at l2
                | cons b v2'' => simp at ht'; simp [ht'.1]
            simp only [List.getD_cons_zero, Nat.zero_add, List.getD_cons_succ, this]
          rw [hs]
      · simp at hyx

theorem kProd_replicate (ω : ℕ → Fin 3) (N : ℕ) : kProd ω (List.replicate N true) = 1 := by
  unfold kProd
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  unfold kElt
  rw [if_pos]
  simp only [Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hi)]
  simp

theorem qElt_replicate (ω : ℕ → Fin 3) (N : ℕ) : qElt ω (List.replicate N true) = gen ω .c := by
  unfold qElt; rw [kProd_replicate]; simp

theorem H1_replicate (N : ℕ) : H1 (List.replicate N true) := fun i h _ => by simp

theorem H2_replicate (ω : ℕ → Fin 3) (N : ℕ) : H2 ω (List.replicate N true) := fun i h hf => by
  simp at hf

/-! ### `|1^∞ ∧ v|` -/

theorem take_of_le_commonPrefixLength (v : List Bool) (p : ℕ)
    (h : p ≤ commonPrefixLength v oneRay) : p ≤ v.length ∧ v.take p = List.replicate p true := by
  unfold commonPrefixLength at h
  have hro : rayPrefix oneRay v.length = List.replicate v.length true := by
    apply List.ext_getElem <;> simp [rayPrefix, oneRay]
  rw [hro] at h
  set l := (v.zip (List.replicate v.length true)).takeWhile fun p => p.1 = p.2
  have hpre : l <+: v.zip (List.replicate v.length true) := List.takeWhile_prefix _
  have hl : l.length ≤ v.length := by
    have := hpre.length_le; simpa using this
  refine ⟨by omega, ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_replicate]
    have hi : i < l.length := by simp at h2; omega
    have hmem : l[i] ∈ l := List.getElem_mem hi
    have hP := List.mem_takeWhile_imp hmem
    have heq : l[i] = (v.zip (List.replicate v.length true))[i]'(by
        have := hpre.length_le; omega) := hpre.getElem hi
    rw [heq] at hP
    simpa using hP

/-! ### Two substitution stacks side by side -/

/-- Both fix level `r`, with sections `(W₁, W₂)` or `(aW₁a, aW₂a)` at each vertex. -/
def GoodPair (W1 W2 : BinaryTreeAut) (r : ℕ) (g1 g2 : BinaryTreeAut) : Prop :=
  ∀ x : List Bool, x.length = r → x <• g1 = x ∧ x <• g2 = x ∧
    ((sec g1 x = W1 ∧ sec g2 x = W2) ∨
      (sec g1 x = grigA * W1 * grigA ∧ sec g2 x = grigA * W2 * grigA))

theorem conj_conj (W : BinaryTreeAut) : grigA * (grigA * W * grigA) * grigA = W := by
  simp only [← mul_assoc, grigA_mul_self, one_mul]
  rw [mul_assoc, grigA_mul_self, mul_one]

theorem goodPair_conj (W1 W2 : BinaryTreeAut) (r : ℕ) (g1 g2 : BinaryTreeAut)
    (hg : GoodPair W1 W2 r g1 g2) :
    GoodPair W1 W2 r (grigA * g1 * grigA) (grigA * g2 * grigA) := by
  intro x hx
  cases x with
  | nil =>
    have := (hg [] hx).2.2
    simp only [sec_nil] at this ⊢
    refine ⟨nil_smul _, nil_smul _, ?_⟩
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · left; rw [h1, h2, conj_conj, conj_conj]; exact ⟨rfl, rfl⟩
  | cons z x' =>
    have h1 := hg ((!z) :: x') (by simpa using hx)
    have hza : (z :: x') <• grigA = ((!z) :: x') := by
      rw [vertex_smul_grigA]; rfl
    have hza' : ((!z) :: x') <• grigA = (z :: x') := by
      rw [vertex_smul_grigA]; simp [grigAFun]
    have hs : ∀ g, ((!z) :: x') <• g = ((!z) :: x') →
        sec (grigA * g * grigA) (z :: x') = sec g ((!z) :: x') := by
      intro g hg'
      rw [sec_mul, sec_mul, sec_grigA_cons, hza, one_mul, vertex_smul_mul, hza, hg',
        sec_grigA_cons, mul_one]
    refine ⟨?_, ?_, ?_⟩
    · rw [vertex_smul_mul, vertex_smul_mul, hza, h1.1, hza']
    · rw [vertex_smul_mul, vertex_smul_mul, hza, h1.2.1, hza']
    · rw [hs g1 h1.1, hs g2 h1.2.1]
      exact h1.2.2

theorem goodPair_zfold (ω : ℕ → Fin 3) (j : ℕ) (w1 w2 : FreeGroup APair)
    (hκ1 : chi (BCD.killedBy (ω (j - 1))) w1 = 1) (hκ2 : chi (BCD.killedBy (ω (j - 1))) w2 = 1) :
    ∀ r m, m + r = j → GoodPair (evalFree ω j w1) (evalFree ω j w2) r
      (evalFree ω m (zfold ω m r w1)) (evalFree ω m (zfold ω m r w2)) := by
  intro r
  induction r with
  | zero =>
    intro m hm x hx
    rw [List.length_eq_zero_iff.mp hx, sec_nil, sec_nil]
    subst hm
    exact ⟨nil_smul _, nil_smul _, Or.inl ⟨rfl, rfl⟩⟩
  | succ r ih =>
    intro m hm
    have hg' := ih (m + 1) (by omega)
    have hswap : ∀ w : FreeGroup APair, chi (BCD.killedBy (ω (j - 1))) w = 1 →
        rootSwap (evalFree ω m (zetaFree (ω m) (zfold ω (m + 1) r w))) = false := by
      intro w hκ
      apply rootSwap_eq_of_bit
      have := bit_zfold ω w r m
      rw [zfold] at this
      rw [this, show m + r = j - 1 by omega, hκ]
    have hd : ∀ w : FreeGroup APair, chi (BCD.killedBy (ω (j - 1))) w = 1 →
        sec (evalFree ω m (zetaFree (ω m) (zfold ω (m + 1) r w))) [false] =
            grigA * evalFree ω (m + 1) (zfold ω (m + 1) r w) * grigA ∧
          sec (evalFree ω m (zetaFree (ω m) (zfold ω (m + 1) r w))) [true] =
            evalFree ω (m + 1) (zfold ω (m + 1) r w) := by
      intro w hκ
      obtain ⟨-, h0, h1⟩ := dec_evalFree ω m (zfold ω (m + 1) r w)
      rw [hswap w hκ] at h0 h1
      simp only [Bool.false_eq_true, if_false, mul_one] at h0 h1
      exact ⟨h0, h1⟩
    have hgood0 := goodPair_conj _ _ r _ _ hg'
    intro x hx
    obtain ⟨y, x', rfl⟩ : ∃ y x', x = y :: x' := by
      cases x with
      | nil => simp at hx
      | cons y x' => exact ⟨y, x', rfl⟩
    have hx' : x'.length = r := by simpa using hx
    have hz : ∀ w, zfold ω m (r + 1) w = zetaFree (ω m) (zfold ω (m + 1) r w) := fun _ => rfl
    rw [hz, hz]
    cases y
    · obtain ⟨a1, a2, a3⟩ := hgood0 x' hx'
      refine ⟨?_, ?_, ?_⟩
      · rw [cons_smul, hswap w1 hκ1, (hd w1 hκ1).1, a1]; rfl
      · rw [cons_smul, hswap w2 hκ2, (hd w2 hκ2).1, a2]; rfl
      · rw [sec_cons _ false x', sec_cons _ false x', (hd w1 hκ1).1, (hd w2 hκ2).1]; exact a3
    · obtain ⟨a1, a2, a3⟩ := hg' x' hx'
      refine ⟨?_, ?_, ?_⟩
      · rw [cons_smul, hswap w1 hκ1, (hd w1 hκ1).2, a1]; rfl
      · rw [cons_smul, hswap w2 hκ2, (hd w2 hκ2).2, a2]; rfl
      · rw [sec_cons _ true x', sec_cons _ true x', (hd w1 hκ1).2, (hd w2 hκ2).2]; exact a3

/-! ### The milestone -/

theorem agree_of_agree (g h : BinaryTreeAut) (L : ℕ)
    (hgh : ∀ z : List Bool, z.length = L → z <• g = z <• h) :
    ∀ z : List Bool, z.length = L →
      z <• (grigA * g) = z <• (grigA * h) ∧ z <• (grigA * (grigA * g) * grigA) =
        z <• (grigA * (grigA * h) * grigA) := by
  intro z hz
  have hza : (z <• grigA).length = L := by rw [length_vertex_smul, hz]
  refine ⟨?_, ?_⟩
  · rw [vertex_smul_mul, vertex_smul_mul, hgh _ hza]
  · rw [grigA_mul_grigA_mul, grigA_mul_grigA_mul, vertex_smul_mul, vertex_smul_mul, hgh z hz]

end ConstrFact714

end ErschlerZheng
end

section
open scoped RightActions commutatorElement
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrFact714
open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
theorem solution (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (γ : Garrido.BinaryTreeAut)
    (hγ : γ ∈ fSet D ω k j n) (u : List Bool) (hu : u.length = n + D + 1) :
    u <• γ = u <• seqG ω j := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  unfold fSet at hγ
  rw [if_pos ⟨hj, hjn, hjn'⟩] at hγ
  obtain ⟨v, hv, hpre, rfl⟩ := hγ
  have hkn := hk.2 n (by omega) hn
  have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
  obtain ⟨hv0, hv1, hv2⟩ := vSet_props D ω hω j (2 * k n) h2k v hv
  obtain ⟨w1, hw1, hb1, -, -⟩ := exists_free_word D ω hω j (2 * k n) h2k v hv
  have hg1 := gTilde_eq D ω hω j hj1 v w1 hw1
  have hg2 := seqG_eq ω j
  have hpair : seqPair ω j = .ac := by simp [seqPair, hj]
  rw [hpair] at hg2
  have hκ1 : chi (BCD.killedBy (ω (j - 1))) w1 = 1 := by rw [hj]; exact hb1
  have hκ2 : chi (BCD.killedBy (ω (j - 1))) (FreeGroup.of APair.ac) = 1 := by
    rw [hj]; simp [chi, pairLetter, BCD.killedBy]
  have hgp := goodPair_zfold ω j w1 _ hκ1 hκ2 j 0 (by omega)
  rw [← hg1, ← hg2, hw1] at hgp
  have hW2 : evalFree ω j (FreeGroup.of APair.ac) = grigA * gen (shiftSeq ω j) .c := by
    rw [evalFree_of, evalWord_toWord]; rfl
  rw [hW2] at hgp
  -- 𝔠 and c agree on level p + 1
  set p := n - j + D
  obtain ⟨hpl, hpt⟩ := take_of_le_commonPrefixLength v p hpre
  have hagree : ∀ z : List Bool, z.length = p + 1 → z <• cElt ω j v = z <• gen (shiftSeq ω j) .c := by
    intro z hz
    rw [cElt_eq_qElt ω j v hv0, ← qElt_replicate (shiftSeq ω j) v.length]
    exact qElt_agree p _ v _ hv1 hv2 (H1_replicate _) (H2_replicate _ _) hpl (by simp; omega)
      (by rw [hpt, List.take_replicate, min_eq_left hpl]) z hz
  have hagree' := agree_of_agree _ _ (p + 1) hagree
  -- split `u` at level `j`
  have hsplit : u = u.take j ++ u.drop j := (List.take_append_drop j u).symm
  have hlt : (u.take j).length = j := by simp [hu]; omega
  have hld : (u.drop j).length = p + 1 := by simp [hu]; omega
  obtain ⟨f1, f2, hs⟩ := hgp (u.take j) hlt
  rw [hsplit, append_vertex_smul, append_vertex_smul, f1, f2]
  congr 1
  rcases hs with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · rw [s1, s2]; exact (hagree' _ hld).1
  · rw [s1, s2]; exact (hagree' _ hld).2
end
