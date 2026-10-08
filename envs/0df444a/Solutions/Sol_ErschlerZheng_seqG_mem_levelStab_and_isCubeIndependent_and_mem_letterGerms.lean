-- Prove2me | solution 1 for ErschlerZheng.seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T03:56:26.406707+00:00
-- url     : https://prove2.me/submissions/65356dd1-1e4c-45e0-a526-b6e869b32948

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_isCubeIndependent_of_mem_levelStab_of_sec_smul_ne
import Theorems.Thm_ErschlerZheng_forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const

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

theorem evalFree_zero_mem (ω : ℕ → Fin 3) (w : FreeGroup APair) :
    evalFree ω 0 w ∈ grigorchuk ω := by
  have : (evalFree ω 0).range ≤ grigorchuk ω := by
    apply FreeGroup.range_lift_le
    rintro _ ⟨p, rfl⟩
    show evalWord ω 0 p.toWord ∈ grigorchuk ω
    rw [evalWord_toWord, shiftSeq_zero]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · simp [gens]
    · cases p <;> simp [gens, pairLetter]
  exact this ⟨w, rfl⟩

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

/-! ### Free-group words from even-length words -/

/-- The parity of the number of letters `aκ`. -/
def chi (κ : BCD) : FreeGroup APair →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun p => Multiplicative.ofAdd (if pairLetter p = κ then 1 else 0)

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

/-- `g` fixes level `r` and its sections there are `W` or `a W a`. -/
def Good (W : BinaryTreeAut) (r : ℕ) (g : BinaryTreeAut) : Prop :=
  ∀ x : List Bool, x.length = r → x <• g = x ∧ (sec g x = W ∨ sec g x = grigA * W * grigA)

theorem good_conj (W : BinaryTreeAut) (r : ℕ) (g : BinaryTreeAut) (hg : Good W r g) :
    Good W r (grigA * g * grigA) := by
  intro x hx
  cases x with
  | nil =>
    have := (hg [] hx).2
    rw [sec_nil] at this ⊢
    refine ⟨nil_smul _, ?_⟩
    rcases this with h | h
    · right; rw [h]
    · left; rw [h]
      simp only [← mul_assoc, grigA_mul_self, one_mul]
      rw [mul_assoc, grigA_mul_self, mul_one]
  | cons z x' =>
    have h1 := hg ((!z) :: x') (by simpa using hx)
    have hza : (z :: x') <• grigA = ((!z) :: x') := by
      rw [vertex_smul_grigA]; rfl
    have hza' : ((!z) :: x') <• grigA = (z :: x') := by
      rw [vertex_smul_grigA]; simp [grigAFun]
    refine ⟨?_, ?_⟩
    · rw [vertex_smul_mul, vertex_smul_mul, hza, h1.1, hza']
    · rw [sec_mul, sec_mul, sec_grigA_cons, hza, one_mul, vertex_smul_mul, hza, h1.1,
        sec_grigA_cons, mul_one]
      exact h1.2

theorem good_zfold (ω : ℕ → Fin 3) (j : ℕ) (w : FreeGroup APair)
    (hκ : chi (BCD.killedBy (ω (j - 1))) w = 1) :
    ∀ r m, m + r = j → Good (evalFree ω j w) r (evalFree ω m (zfold ω m r w)) := by
  intro r
  induction r with
  | zero =>
    intro m hm x hx
    rw [List.length_eq_zero_iff.mp hx, sec_nil]
    subst hm
    exact ⟨nil_smul _, Or.inl rfl⟩
  | succ r ih =>
    intro m hm
    have hg' := ih (m + 1) (by omega)
    set u := zfold ω (m + 1) r w
    have hswap : rootSwap (evalFree ω m (zetaFree (ω m) u)) = false := by
      apply rootSwap_eq_of_bit
      have := bit_zfold ω w r m
      rw [zfold] at this
      rw [this, show m + r = j - 1 by omega, hκ]
    obtain ⟨-, h0, h1⟩ := dec_evalFree ω m u
    rw [hswap] at h0 h1
    simp only [Bool.false_eq_true, if_false, mul_one] at h0 h1
    have hgood0 := good_conj _ r _ hg'
    intro x hx
    obtain ⟨y, x', rfl⟩ : ∃ y x', x = y :: x' := by
      cases x with
      | nil => simp at hx
      | cons y x' => exact ⟨y, x', rfl⟩
    have hx' : x'.length = r := by simpa using hx
    have hz : zfold ω m (r + 1) w = zetaFree (ω m) u := rfl
    rw [hz]
    cases y
    · obtain ⟨a1, a2⟩ := hgood0 x' hx'
      refine ⟨?_, ?_⟩
      · rw [cons_smul, hswap, h0, a1]; rfl
      · rw [sec_cons, h0]; exact a2
    · obtain ⟨a1, a2⟩ := hg' x' hx'
      refine ⟨?_, ?_⟩
      · rw [cons_smul, hswap, h1, a1]; rfl
      · rw [sec_cons, h1]; exact a2

/-! ### The free word for `a𝔠` and the tail condition -/

theorem tail_of_fr (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ) (i : Fin 3) :
    ∃ m, k < m ∧ ω m ≠ i := by
  obtain ⟨m, hm, h2, h1, -⟩ := hω (k + 1)
  have hD : 1 ≤ D := by omega
  have : k + 1 ≤ (k + 1) * D := Nat.le_mul_of_pos_right _ hD
  by_cases hi : i = 2
  · exact ⟨(k + 1) * D + m + 2, by omega, by rw [h1, hi]; decide⟩
  · exact ⟨(k + 1) * D + m, by omega, by rw [h2]; exact Ne.symm hi⟩

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

theorem chi_seqPair (ω : ℕ → Fin 3) (n : ℕ) :
    chi (BCD.killedBy (ω (n - 1))) (FreeGroup.of (seqPair ω n)) = 1 := by
  unfold seqPair chi
  rw [FreeGroup.lift_apply_of]
  rcases fin3_cases (ω (n - 1)) with h | h | h <;> simp [h, pairLetter, BCD.killedBy] <;> rfl

theorem evalFree_seqPair (ω : ℕ → Fin 3) (n : ℕ) :
    evalFree ω n (FreeGroup.of (seqPair ω n)) =
      evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] := by
  rw [evalFree_of]
  unfold seqPair
  split_ifs <;> rfl

/-- Along `1^r` the section is the word itself. -/
theorem sec_replicate_zfold (ω : ℕ → Fin 3) (j : ℕ) (w : FreeGroup APair)
    (hκ : chi (BCD.killedBy (ω (j - 1))) w = 1) :
    ∀ r m, m + r = j →
      sec (evalFree ω m (zfold ω m r w)) (List.replicate r true) = evalFree ω j w := by
  intro r
  induction r with
  | zero => intro m hm; subst hm; rw [List.replicate_zero, sec_nil]; rfl
  | succ r ih =>
    intro m hm
    set u := zfold ω (m + 1) r w
    have hswap : rootSwap (evalFree ω m (zetaFree (ω m) u)) = false := by
      apply rootSwap_eq_of_bit
      have := bit_zfold ω w r m
      rw [zfold] at this
      rw [this, show m + r = j - 1 by omega, hκ]
    obtain ⟨-, -, h1⟩ := dec_evalFree ω m u
    rw [hswap] at h1
    simp only [Bool.false_eq_true, if_false, mul_one] at h1
    have hz : zfold ω m (r + 1) w = zetaFree (ω m) u := rfl
    rw [hz, List.replicate_succ, sec_cons, h1, ih (m + 1) (by omega)]

/-! ### Exchanging the letters `1` and `2` -/

/-- The permutation `1 ↔ 2` of the letters. -/
def swapBC : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

theorem swapBC_swapBC (i : Fin 3) : swapBC (swapBC i) = i := by
  rcases fin3_cases i with rfl | rfl | rfl <;> rfl

theorem letterValue_swapBC (i : Fin 3) :
    letterValue (swapBC i) .b = letterValue i .c ∧ letterValue (swapBC i) .c = letterValue i .b ∧
      letterValue (swapBC i) .d = letterValue i .d := by
  rcases fin3_cases i with rfl | rfl | rfl <;> decide

theorem genFun_swapBC (ω : ℕ → Fin 3) (w : List Bool) :
    genFun (swapBC ∘ ω) .b w = genFun ω .c w ∧ genFun (swapBC ∘ ω) .c w = genFun ω .b w ∧
      genFun (swapBC ∘ ω) .d w = genFun ω .d w := by
  induction w generalizing ω with
  | nil => simp [genFun]
  | cons x w ih =>
    obtain ⟨l1, l2, l3⟩ := letterValue_swapBC (ω 0)
    cases x
    · simp [genFun, Function.comp, l1, l2, l3]
    · have e : shiftSeq (swapBC ∘ ω) 1 = swapBC ∘ shiftSeq ω 1 := rfl
      obtain ⟨i1, i2, i3⟩ := ih (shiftSeq ω 1)
      simp only [genFun, e, i1, i2, i3, and_self]

theorem gen_swapBC (ω : ℕ → Fin 3) :
    gen (swapBC ∘ ω) .b = gen ω .c ∧ gen (swapBC ∘ ω) .c = gen ω .b ∧
      gen (swapBC ∘ ω) .d = gen ω .d := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Subtype.ext <;> apply Equiv.ext <;> intro w
  · exact (genFun_swapBC ω w).1
  · exact (genFun_swapBC ω w).2.1
  · exact (genFun_swapBC ω w).2.2

theorem grigorchuk_swapBC (ω : ℕ → Fin 3) : grigorchuk (swapBC ∘ ω) = grigorchuk ω := by
  unfold grigorchuk gens
  obtain ⟨h1, h2, h3⟩ := gen_swapBC ω
  rw [h1, h2, h3]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem letterGerms_swapBC (ω : ℕ → Fin 3) : letterGerms (swapBC ∘ ω) .b = letterGerms ω .c := by
  unfold letterGerms germLetterSubgroup
  rw [grigorchuk_swapBC, (gen_swapBC ω).1]

theorem shiftSeq_swapBC (ω : ℕ → Fin 3) (n : ℕ) :
    shiftSeq (swapBC ∘ ω) n = swapBC ∘ shiftSeq ω n := rfl

theorem not_eventually_const (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (f : Fin 3 → Fin 3)
    (hf : ∀ i, f (f i) = i) : ¬ ∃ i : Fin 3, ∀ᶠ k in Filter.atTop, (f ∘ ω) k = i := by
  rintro ⟨i, hi⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hi
  obtain ⟨m, hm, hne⟩ := tail_of_fr D ω hω N (f i)
  apply hne
  have := hN m (by omega)
  simp only [Function.comp] at this
  rw [← this, hf]

/-! ### Generators that differ -/

theorem sec_gen_replicate_true' (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

theorem sec_gen_one_zero (ω : ℕ → Fin 3) (γ : BCD) (m : ℕ) :
    sec (gen ω γ) (List.replicate m true ++ [false]) = letterElt (ω m) γ := by
  rw [sec_append, sec_gen_replicate_true', sec_gen_false]
  simp [shiftSeq]

theorem grigA_ne_one : grigA ≠ 1 := by
  intro h
  have := rootSwap_grigA
  rw [h, rootSwap_one] at this
  exact Bool.noConfusion this

theorem letterValue_of_letterElt_eq {i : Fin 3} {γ γ' : BCD}
    (h : letterElt i γ = letterElt i γ') : letterValue i γ = letterValue i γ' := by
  unfold letterElt at h
  cases h1 : letterValue i γ <;> cases h2 : letterValue i γ' <;> simp_all
  · exact grigA_ne_one h.symm
  · exact grigA_ne_one h

theorem gen_c_not_mem (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (L : ℕ) :
    gen (shiftSeq ω L) .c ∉ ({1, grigA, gen (shiftSeq ω L) .b} : Set BinaryTreeAut) := by
  intro hmem
  rcases hmem with h | h | h
  · obtain ⟨m, hm, hne⟩ := tail_of_fr D ω hω L 1
    have := sec_gen_one_zero (shiftSeq ω L) .c (m - L)
    rw [h, sec_one] at this
    have hv : letterValue ((shiftSeq ω L) (m - L)) .c = false := by
      unfold letterElt at this
      split_ifs at this with hh
      · exact absurd this.symm grigA_ne_one
      · simpa using hh
    simp only [shiftSeq, show m - L + L = m by omega] at hv
    revert hv hne
    generalize ω m = i
    revert i
    decide
  · have h1 := rootSwap_gen (shiftSeq ω L) .c
    rw [h, rootSwap_grigA] at h1
    exact Bool.noConfusion h1
  · obtain ⟨m, hm, hne⟩ := tail_of_fr D ω hω L 0
    have h1 := sec_gen_one_zero (shiftSeq ω L) .c (m - L)
    have h2 := sec_gen_one_zero (shiftSeq ω L) .b (m - L)
    rw [h] at h1
    have hv := letterValue_of_letterElt_eq (h2.symm.trans h1)
    simp only [shiftSeq, show m - L + L = m by omega] at hv
    revert hv hne
    generalize ω m = i
    revert i
    decide

/-! ### The milestone -/

theorem seq_good (ω : ℕ → Fin 3) (n : ℕ) :
    Good (evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b]) n (seqG ω n) := by
  have := good_zfold ω n _ (chi_seqPair ω n) n 0 (by omega)
  rw [evalFree_seqPair] at this
  rw [seqG_eq]
  exact this

theorem evalWord_pair (ω : ℕ → Fin 3) (n : ℕ) (x : Gen4) (γ : BCD) (hx : x = bcdGen γ) :
    evalWord ω n [.a, x] = grigA * gen (shiftSeq ω n) γ := by
  subst hx; cases γ <;> simp [evalWord, bcdGen]

/-- The letter `γ` of (7.1). -/
def seqLetter (ω : ℕ → Fin 3) (n : ℕ) : BCD := if ω (n - 1) = 2 then .c else .b

theorem evalWord_seq (ω : ℕ → Fin 3) (n : ℕ) :
    evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] =
      grigA * gen (shiftSeq ω n) (seqLetter ω n) := by
  apply evalWord_pair
  unfold seqLetter; split_ifs <;> rfl

theorem sec_seqG_succ (ω : ℕ → Fin 3) (n : ℕ) (v : List Bool) (hv : v.length = n + 1) :
    sec (seqG ω n) v ∈ ({1, grigA, gen (shiftSeq ω (n + 1)) (seqLetter ω n)} :
      Set BinaryTreeAut) := by
  obtain ⟨v1, x, rfl⟩ : ∃ v1 x, v = v1 ++ [x] := by
    rcases List.eq_nil_or_concat v with h | ⟨v1, x, h⟩
    · subst h; simp at hv
    · exact ⟨v1, x, by rw [h, List.concat_eq_append]⟩
  have hv1 : v1.length = n := by simpa using hv
  rw [sec_append]
  have hG : ∀ y : Bool, sec (gen (shiftSeq ω n) (seqLetter ω n)) [y] ∈
      ({1, grigA, gen (shiftSeq ω (n + 1)) (seqLetter ω n)} : Set BinaryTreeAut) := by
    intro y
    cases y
    · rw [sec_gen_false]; unfold letterElt; split_ifs <;> simp
    · rw [sec_gen_true, shiftSeq_shiftSeq, Nat.add_comm]; simp
  rcases (seq_good ω n v1 hv1).2 with h | h <;> rw [h, evalWord_seq]
  · rw [sec_mul, sec_grigA, one_mul, singleton_smul, rootSwap_grigA]
    exact hG _
  · rw [grigA_mul_grigA_mul, sec_mul, singleton_smul, sec_grigA, mul_one]
    exact hG _

theorem levelStab_good (ω : ℕ → Fin 3) (n : ℕ) :
    seqG ω n ∈ levelStab (grigorchuk ω) n := by
  refine ⟨?_, fun v hv => (seq_good ω n v hv).1⟩
  rw [seqG_eq]; exact evalFree_zero_mem ω _

end ConstrSeq

end ErschlerZheng
end

section
open scoped RightActions commutatorElement
open Garrido
open ErschlerZheng
open ErschlerZheng.ConstrSeq
open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) :
    (∀ n, 1 ≤ n → seqG ω n ∈ levelStab (grigorchuk ω) n ∧
      ∀ v : List Bool, v.length = n →
        sec (seqG ω n) v = evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] ∨
          sec (seqG ω n) v =
            Garrido.grigA * evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b] * Garrido.grigA) ∧
    IsCubeIndependent (orbitOne ω) (fun _ => 1) (seqG ω) ∧
    ∀ n, 1 ≤ n →
      (ω (n - 1) ≠ 2 → ∀ x ∈ orbitOne ω, (seqG ω n, x) ∈ letterGerms ω .b) ∧
      (ω (n - 1) = 2 → (∀ x ∈ orbitOne ω, (seqG ω n, x) ∈ letterGerms ω .c) ∧
        ∃ x ∈ orbitOne ω, (seqG ω n, x) ∉ letterGerms ω .b) := by
  have hmemG : ∀ n, seqG ω n ∈ grigorchuk ω := fun n => (levelStab_good ω n).1
  refine ⟨fun n _ => ⟨levelStab_good ω n, fun v hv => (seq_good ω n v hv).2⟩, ?_, ?_⟩
  · apply isCubeIndependent_of_mem_levelStab_of_sec_smul_ne (grigorchuk ω) (seqG ω)
      (fun n _ => levelStab_good ω n)
    intro n _ v hv x
    have hsw : ∀ h : BinaryTreeAut, rootSwap h = true → [x] <• h ≠ [x] := by
      intro h hh
      rw [singleton_smul, hh]
      cases x <;> simp
    rcases (seq_good ω n v hv).2 with h | h <;> rw [h, evalWord_seq] <;> apply hsw
    · rw [rootSwap_mul, rootSwap_grigA, rootSwap_gen]; rfl
    · rw [rootSwap_mul, rootSwap_mul, rootSwap_mul, rootSwap_grigA, rootSwap_gen]; rfl
  · intro n hn
    have hB4 := forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const ω
      (by simpa using not_eventually_const D ω hω id (fun _ => rfl)) (seqG ω n) (hmemG n)
    refine ⟨fun hne => ?_, fun h2 => ⟨?_, ?_⟩⟩
    · have hl : seqLetter ω n = .b := by simp [seqLetter, hne]
      apply hB4.2
      refine ⟨n + 1, fun v hv => ?_⟩
      have := sec_seqG_succ ω n v hv
      rwa [hl] at this
    · have hl : seqLetter ω n = .c := by simp [seqLetter, h2]
      have hB4' := forall_mem_letterGerms_b_iff_exists_sec_mem_of_not_eventually_const
        (swapBC ∘ ω) (not_eventually_const D ω hω swapBC swapBC_swapBC) (seqG ω n)
        (by rw [grigorchuk_swapBC]; exact hmemG n)
      have horb : orbitOne (swapBC ∘ ω) = orbitOne ω := by
        unfold orbitOne; rw [grigorchuk_swapBC]
      rw [horb, letterGerms_swapBC] at hB4'
      apply hB4'.2
      refine ⟨n + 1, fun v hv => ?_⟩
      have := sec_seqG_succ ω n v hv
      rw [hl] at this
      rw [shiftSeq_swapBC, (gen_swapBC _).1]
      exact this
    · by_contra hall
      push Not at hall
      obtain ⟨N, hN⟩ := hB4.1 hall
      -- the property propagates to deeper levels
      have hdeep : ∀ t, ∀ v : List Bool, v.length = N + t →
          sec (seqG ω n) v ∈ ({1, grigA, gen (shiftSeq ω (N + t)) .b} : Set BinaryTreeAut) := by
        intro t
        induction t with
        | zero => exact hN
        | succ t ih =>
          intro v hv
          obtain ⟨v1, x, rfl⟩ : ∃ v1 x, v = v1 ++ [x] := by
            rcases List.eq_nil_or_concat v with h | ⟨v1, x, h⟩
            · subst h; simp at hv
            · exact ⟨v1, x, by rw [h, List.concat_eq_append]⟩
          rw [sec_append]
          rcases ih v1 (by simp at hv; omega) with h | h | h <;> rw [h]
          · simp [sec_one]
          · simp [sec_grigA]
          · cases x
            · rw [sec_gen_false]; unfold letterElt; split_ifs <;> simp
            · rw [sec_gen_true, shiftSeq_shiftSeq]
              simp [show 1 + (N + t) = N + (t + 1) by omega]
      have hc : seqLetter ω n = .c := by simp [seqLetter, h2]
      set L := max N (n + 1) with hL
      have hz := hdeep (L - N) (List.replicate n true ++ [false] ++ List.replicate (L - (n + 1)) true)
        (by simp; omega)
      rw [show N + (L - N) = L by omega] at hz
      have hsec : sec (seqG ω n)
          (List.replicate n true ++ [false] ++ List.replicate (L - (n + 1)) true) =
            gen (shiftSeq ω L) .c := by
        rw [sec_append, sec_append]
        have h1 := sec_replicate_zfold ω n _ (chi_seqPair ω n) n 0 (by omega)
        rw [← seqG_eq, evalFree_seqPair, evalWord_seq, hc] at h1
        rw [h1, sec_mul, sec_grigA, one_mul, singleton_smul, rootSwap_grigA]
        simp only [Bool.false_bne, Bool.not_false]
        rw [sec_gen_true, sec_gen_replicate_true', shiftSeq_shiftSeq, shiftSeq_shiftSeq]
        congr 2
        omega
      rw [hsec] at hz
      exact gen_c_not_mem D ω hω L hz
end
