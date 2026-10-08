-- Prove2me | solution 1 for ErschlerZheng.evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T01:05:58.931366+00:00
-- url     : https://prove2.me/submissions/094f0ebf-f4e1-4f7f-a189-c905575b860e

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq

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

/-- `σ_k(g)`: the parity of the number of level-`k` vertices whose section swaps level 1. -/
noncomputable def levelPar (k : ℕ) (g : BinaryTreeAut) : ZMod 2 :=
  ∑ v : List.Vector Bool k, bit (sec g v.1)

/-- The action of `g` on level `k`, as a permutation of `List.Vector Bool k`. -/
def levelEquiv (k : ℕ) (g : BinaryTreeAut) : List.Vector Bool k ≃ List.Vector Bool k where
  toFun v := ⟨v.1 <• g, by rw [length_vertex_smul]; exact v.2⟩
  invFun v := ⟨v.1 <• g⁻¹, by rw [length_vertex_smul]; exact v.2⟩
  left_inv v := Subtype.ext (vertex_smul_smul_inv g v.1)
  right_inv v := Subtype.ext (vertex_smul_inv_smul g v.1)

theorem levelPar_mul (k : ℕ) (g h : BinaryTreeAut) :
    levelPar k (g * h) = levelPar k g + levelPar k h := by
  unfold levelPar
  simp_rw [sec_mul, bit_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Fintype.sum_equiv (levelEquiv k g) _ _ (fun v => rfl)

theorem levelPar_one (k : ℕ) : levelPar k 1 = 0 := by
  simp [levelPar, sec_one, bit_one]

theorem levelPar_inv (k : ℕ) (g : BinaryTreeAut) : levelPar k g⁻¹ = levelPar k g := by
  have h := levelPar_mul k g g⁻¹
  rw [mul_inv_cancel, levelPar_one] at h
  have : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  exact this _ _ h

theorem levelPar_zero (g : BinaryTreeAut) : levelPar 0 g = bit g := by
  unfold levelPar
  rw [Fintype.sum_eq_single List.Vector.nil (fun v hv => absurd (Subsingleton.elim v _) hv)]
  rw [show (List.Vector.nil : List.Vector Bool 0).1 = [] from rfl, sec_nil]

/-- Level `k + 1` splits into the subtrees of `0` and `1`. -/
def splitEquiv (k : ℕ) : Bool × List.Vector Bool k ≃ List.Vector Bool (k + 1) where
  toFun p := p.1 ::ᵥ p.2
  invFun v := (v.head, v.tail)
  left_inv p := by simp
  right_inv v := List.Vector.cons_head_tail v

theorem levelPar_succ (k : ℕ) (g : BinaryTreeAut) :
    levelPar (k + 1) g = levelPar k (sec g [false]) + levelPar k (sec g [true]) := by
  unfold levelPar
  rw [← Fintype.sum_equiv (splitEquiv k) (fun p => bit (sec g (p.1 ::ᵥ p.2).1)) _
    (fun p => rfl), Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun u _ => ?_ <;>
    rw [show ((_ ::ᵥ u : List.Vector Bool (k + 1))).1 = _ :: u.1 from rfl, sec_cons]

theorem levelPar_grigA (k : ℕ) : levelPar k grigA = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [levelPar_zero, bit, rootSwap_grigA]
  | succ k => simp [levelPar_succ, sec_grigA, levelPar_one]

/-- `[ω_k(γ) = a]` as an element of `ZMod 2`. -/
def lv (i : Fin 3) (γ : BCD) : ZMod 2 := if letterValue i γ then 1 else 0

theorem levelPar_letterElt (k : ℕ) (i : Fin 3) (γ : BCD) :
    levelPar k (letterElt i γ) = if k = 0 then lv i γ else 0 := by
  unfold letterElt lv
  by_cases h : letterValue i γ
  · simp [h, levelPar_grigA]
  · simp [h, levelPar_one]

theorem levelPar_gen (k : ℕ) (ω : ℕ → Fin 3) (γ : BCD) :
    levelPar (k + 1) (gen ω γ) = lv (ω k) γ := by
  induction k generalizing ω with
  | zero =>
    rw [levelPar_succ, sec_gen_false, sec_gen_true, levelPar_letterElt, levelPar_zero, bit,
      rootSwap_gen]
    simp
  | succ k ih =>
    rw [levelPar_succ, sec_gen_false, sec_gen_true, levelPar_letterElt, ih]
    simp [shiftSeq]

theorem levelPar_zero_gen (ω : ℕ → Fin 3) (γ : BCD) : levelPar 0 (gen ω γ) = 0 := by
  rw [levelPar_zero, bit, rootSwap_gen]; simp

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

theorem lv_eq (i : Fin 3) (γ : BCD) :
    lv i γ = 1 + if γ = BCD.killedBy i then 1 else 0 := by
  unfold lv letterValue
  by_cases h : γ = BCD.killedBy i <;> simp [h]
  decide

/-- The parity of `ζ_{ω_n}(w)` as levels of `w`: `[γ = κ_{ω_n}] = 1 + Σ_{j ∈ J} [ω_{n+1+j}(γ) = a]`. -/
theorem exists_levels (ω : ℕ → Fin 3) (n : ℕ)
    (hω : ∀ i : Fin 3, i ≠ ω n → ∃ k, n < k ∧ ω k ≠ i) :
    ∃ J : Finset ℕ, ∀ γ : BCD,
      (if γ = BCD.killedBy (ω n) then (1 : ZMod 2) else 0) =
        1 + ∑ j ∈ J, lv (ω (j + n + 1)) γ := by
  by_cases hrec : ∃ k, n < k ∧ ω k = ω n
  · obtain ⟨k, hk, hkω⟩ := hrec
    refine ⟨{k - n - 1}, fun γ => ?_⟩
    rw [Finset.sum_singleton, show k - n - 1 + n + 1 = k by omega, hkω, lv_eq]
    generalize (if γ = BCD.killedBy (ω n) then (1 : ZMod 2) else 0) = x
    have : ∀ y : ZMod 2, y = 1 + (1 + y) := by decide
    exact this x
  · push Not at hrec
    -- the two other letters
    have hex : ∃ i1 i2 : Fin 3, i1 ≠ ω n ∧ i2 ≠ ω n ∧ i1 ≠ i2 := by
      rcases fin3_cases (ω n) with h | h | h <;> rw [h]
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨i1, i2, h1, h2, h12⟩ := hex
    have hthird : ∀ j, n < j → ω j = i1 ∨ ω j = i2 := by
      intro j hj
      have := hrec j hj
      rcases fin3_cases (ω j) with a | a | a <;> rcases fin3_cases (ω n) with b | b | b <;>
        rcases fin3_cases i1 with c | c | c <;> rcases fin3_cases i2 with d | d | d <;>
        simp_all
    obtain ⟨k1, hk1, hk1ω⟩ := hω i1 h1
    obtain ⟨k2, hk2, hk2ω⟩ := hω i2 h2
    have e1 : ω k1 = i2 := (hthird k1 hk1).resolve_left hk1ω
    have e2 : ω k2 = i1 := (hthird k2 hk2).resolve_right hk2ω
    have hne : k1 - n - 1 ≠ k2 - n - 1 := by
      intro h
      have : k1 = k2 := by omega
      rw [this, e2] at e1
      exact h12 e1
    refine ⟨{k1 - n - 1, k2 - n - 1}, fun γ => ?_⟩
    rw [Finset.sum_pair hne, show k1 - n - 1 + n + 1 = k1 by omega,
      show k2 - n - 1 + n + 1 = k2 by omega, e1, e2, lv_eq, lv_eq]
    -- exactly one of the three letters kills γ
    have key : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → ∀ γ : BCD,
        (if γ = BCD.killedBy i then (1 : ZMod 2) else 0) =
          1 + ((1 + if γ = BCD.killedBy l then 1 else 0) +
            (1 + if γ = BCD.killedBy j then 1 else 0)) := by
      intro i j l hij hil hjl γ
      rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
        rcases fin3_cases l with rfl | rfl | rfl <;> cases γ <;>
        first | exact absurd rfl hij | exact absurd rfl hil | exact absurd rfl hjl | decide
    exact key (ω n) i1 i2 (Ne.symm h1) (Ne.symm h2) h12 γ

theorem bit_eq_levels (ω : ℕ → Fin 3) (n : ℕ) (J : Finset ℕ)
    (hJ : ∀ γ : BCD, (if γ = BCD.killedBy (ω n) then (1 : ZMod 2) else 0) =
        1 + ∑ j ∈ J, lv (ω (j + n + 1)) γ)
    (w : FreeGroup APair) :
    bit (evalFree ω n (zetaFree (ω n) w)) =
      levelPar 0 (evalFree ω (n + 1) w) +
        ∑ j ∈ J, levelPar (j + 1) (evalFree ω (n + 1) w) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp [bit_one, levelPar_one]
  | of p =>
    rw [bit_evalFree_zetaFree_of, evalFree_of, evalWord_toWord, hJ]
    have e0 : levelPar 0 (grigA * gen (shiftSeq ω (n + 1)) (pairLetter p)) = 1 := by
      rw [levelPar_mul, levelPar_grigA, levelPar_zero_gen]; simp
    have e1 : ∀ j, levelPar (j + 1) (grigA * gen (shiftSeq ω (n + 1)) (pairLetter p)) =
        lv (ω (j + n + 1)) (pairLetter p) := by
      intro j
      rw [levelPar_mul, levelPar_grigA, levelPar_gen]
      simp only [shiftSeq, Nat.add_one_ne_zero, if_false, zero_add]
      congr 2
    rw [e0]
    simp_rw [e1]
  | inv_of p ih =>
    simp only [map_inv, levelPar_inv]
    rw [← ih]
    unfold bit
    rw [rootSwap_inv]
  | mul x y ihx ihy =>
    simp only [map_mul, bit_mul, levelPar_mul, ihx, ihy, Finset.sum_add_distrib]
    ring

/-- The congruence: two words with the same value have `ζ`-images with the same value. -/
theorem congr_of_tail (ω : ℕ → Fin 3) (n : ℕ)
    (hω : ∀ i : Fin 3, i ≠ ω n → ∃ k, n < k ∧ ω k ≠ i)
    (w₁ w₂ : FreeGroup APair) (h : evalFree ω (n + 1) w₁ = evalFree ω (n + 1) w₂) :
    evalFree ω n (zetaFree (ω n) w₁) = evalFree ω n (zetaFree (ω n) w₂) := by
  obtain ⟨J, hJ⟩ := exists_levels ω n hω
  have hb : bit (evalFree ω n (zetaFree (ω n) w₁)) = bit (evalFree ω n (zetaFree (ω n) w₂)) := by
    rw [bit_eq_levels ω n J hJ, bit_eq_levels ω n J hJ, h]
  have hr : rootSwap (evalFree ω n (zetaFree (ω n) w₁)) =
      rootSwap (evalFree ω n (zetaFree (ω n) w₂)) := by
    unfold bit at hb
    revert hb
    cases rootSwap (evalFree ω n (zetaFree (ω n) w₁)) <;>
      cases rootSwap (evalFree ω n (zetaFree (ω n) w₂)) <;> decide
  obtain ⟨-, a0, a1⟩ := dec_evalFree ω n w₁
  obtain ⟨-, b0, b1⟩ := dec_evalFree ω n w₂
  refine ext_of_rootSwap_sec hr ?_ ?_
  · rw [a0, b0, h, hr]
  · rw [a1, b1, h, hr]

end ZetaHatDev

open GrigBasic ZetaDev ZetaHatDev
theorem zetaHat_evalFree_of_tail (ω : ℕ → Fin 3) (m : ℕ)
    (h : ∀ i : Fin 3, i ≠ ω m → ∃ k, m < k ∧ ω k ≠ i) (w : FreeGroup APair) :
    zetaHat ω m (evalFree ω (m + 1) w) = evalFree ω m (zetaFree (ω m) w) := by
  have hex : ∃ w' : FreeGroup APair, evalFree ω (m + 1) w' = evalFree ω (m + 1) w := ⟨w, rfl⟩
  unfold zetaHat
  rw [dif_pos hex]
  exact congr_of_tail ω m h _ _ hex.choose_spec

/-- The composite `ζ̂_k ∘ ⋯ ∘ ζ̂_{k+r-1}` of the substitutions on values is the value at level `k`
of the substituted word, when the tail condition holds at every level from `k` to `k + r - 1`. -/
theorem foldr_Ico_zetaHat_eq_of_tail (ω : ℕ → Fin 3) (k : ℕ) : ∀ r : ℕ,
    (∀ j, k ≤ j → j < k + r → ∀ i : Fin 3, i ≠ ω j → ∃ m, j < m ∧ ω m ≠ i) →
      ∀ w : FreeGroup APair,
        (List.Ico k (k + r)).foldr (fun j g => zetaHat ω j g) (evalFree ω (k + r) w) =
          evalFree ω k ((List.Ico k (k + r)).foldr (fun j w => zetaFree (ω j) w) w)
  | 0, _, w => by rw [Nat.add_zero, List.Ico.self_empty]; rfl
  | r + 1, h, w => by
    rw [← Nat.add_assoc, List.Ico.succ_top (Nat.le_add_right k r), List.foldr_append,
      List.foldr_append, List.foldr_cons, List.foldr_nil, List.foldr_cons, List.foldr_nil,
      zetaHat_evalFree_of_tail ω (k + r) (h (k + r) (Nat.le_add_right k r) (by omega))]
    exact foldr_Ico_zetaHat_eq_of_tail ω k r (fun j hj hj' => h j hj (by omega)) _

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
set_option linter.unusedSimpArgs false
open ErschlerZheng
open GrigBasic ZetaDev ZetaHatDev
theorem solution (ω : ℕ → Fin 3) (n : ℕ)
    (hω : ∀ i : Fin 3, i ≠ ω n → ∃ k, n < k ∧ ω k ≠ i) :
    (∀ w₁ w₂ : FreeGroup APair, evalFree ω (n + 1) w₁ = evalFree ω (n + 1) w₂ →
      evalFree ω n (zetaFree (ω n) w₁) = evalFree ω n (zetaFree (ω n) w₂)) ∧
    (∀ w : FreeGroup APair, zetaHat ω n (evalFree ω (n + 1) w) = evalFree ω n (zetaFree (ω n) w)) ∧
    (∀ g ∈ (evalFree ω (n + 1)).range, ∀ h ∈ (evalFree ω (n + 1)).range,
      zetaHat ω n (g * h) = zetaHat ω n g * zetaHat ω n h) ∧
    ∀ k ≤ n, (∀ j, k ≤ j → j ≤ n → ∀ i : Fin 3, i ≠ ω j → ∃ m, j < m ∧ ω m ≠ i) →
      ∀ w : FreeGroup APair,
        (List.Ico k (n + 1)).foldr (fun j g => zetaHat ω j g) (evalFree ω (n + 1) w) =
          evalFree ω k ((List.Ico k (n + 1)).foldr (fun j w => zetaFree (ω j) w) w) := by
  have hcongr := congr_of_tail ω n hω
  have hhat := zetaHat_evalFree_of_tail ω n hω
  refine ⟨hcongr, hhat, ?_, ?_⟩
  · rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩
    rw [← map_mul, hhat, hhat, hhat, map_mul, map_mul]
  · intro k hk htail w
    obtain ⟨r, hr⟩ : ∃ r, n + 1 = k + r := ⟨n + 1 - k, by omega⟩
    rw [hr]
    exact foldr_Ico_zetaHat_eq_of_tail ω k r (fun j hj hj' => htail j hj (by omega)) w
end
