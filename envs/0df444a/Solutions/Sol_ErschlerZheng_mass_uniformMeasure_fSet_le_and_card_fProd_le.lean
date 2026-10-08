-- Prove2me | solution 1 for ErschlerZheng.mass_uniformMeasure_fSet_le_and_card_fProd_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T06:51:05.180991+00:00
-- url     : https://prove2.me/submissions/29b8c5fb-bf66-423a-b446-4dce0862786f

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
import Theorems.Thm_ErschlerZheng_sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq
import Theorems.Thm_ErschlerZheng_evalFree_zetaFree_congr_and_zetaHat_evalFree_eq_of_tail_ne
import Theorems.Thm_ErschlerZheng_smul_cElt_eq_self_and_sec_cElt_eq
import Theorems.Thm_ErschlerZheng_sec_list_prod
import Theorems.Thm_ErschlerZheng_schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal
import Theorems.Thm_ErschlerZheng_injOn_gTilde_and_ncard_fSet_eq
import Theorems.Thm_ErschlerZheng_schreierDist_smul_le_of_mem_fSet_and_smul_theta_le

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

/-- The positions `i < q D` with `p D + (i + 1) ∈ I_ω` are `ℓ D + m_{p+ℓ} + 2`, `ℓ < q`. -/
theorem mem_frI_iff (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (p q i : ℕ)
    (hi : i < q * D) :
    p * D + (i + 1) ∈ frI D ω ↔ ∃ ℓ < q, i = ℓ * D + frM D ω (p + ℓ) + 2 := by
  constructor
  · rintro ⟨ℓ', hℓ'⟩
    have h1 := (frM_spec D ω hω ℓ').1
    -- ℓ' ≥ p
    have hp : p ≤ ℓ' := by
      by_contra hlt
      push Not at hlt
      have : (ℓ' + 1) * D ≤ p * D := Nat.mul_le_mul_right D hlt
      have : (ℓ' + 1) * D = ℓ' * D + D := by ring
      omega
    have hq : ℓ' < p + q := by
      by_contra hge
      push Not at hge
      have : (p + q) * D ≤ ℓ' * D := Nat.mul_le_mul_right D hge
      have : (p + q) * D = p * D + q * D := by ring
      omega
    refine ⟨ℓ' - p, by omega, ?_⟩
    have e : p + (ℓ' - p) = ℓ' := by omega
    rw [e]
    have : ℓ' * D = p * D + (ℓ' - p) * D := by
      rw [← Nat.add_mul, e]
    omega
  · rintro ⟨ℓ, hℓ, rfl⟩
    refine ⟨p + ℓ, ?_⟩
    have : (p + ℓ) * D = p * D + ℓ * D := by ring
    omega

/-- The set of free positions of `W^{pD}_{qD}`. -/
def freePos (D : ℕ) (ω : ℕ → Fin 3) (n k : ℕ) : Set ℕ := {i | i < k ∧ n + (i + 1) ∈ frI D ω}

theorem ncard_freePos (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (p q : ℕ) :
    (freePos D ω (p * D) (q * D)).ncard = q := by
  have hD : 3 ≤ D := by have := (frM_spec D ω hω 0).1; omega
  have key : freePos D ω (p * D) (q * D) =
      (fun ℓ => ℓ * D + frM D ω (p + ℓ) + 2) '' Set.Iio q := by
    ext i
    simp only [freePos, Set.mem_setOf_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨hi, hmem⟩
      obtain ⟨ℓ, hℓ, rfl⟩ := (mem_frI_iff D ω hω p q i hi).1 hmem
      exact ⟨ℓ, hℓ, rfl⟩
    · rintro ⟨ℓ, hℓ, rfl⟩
      have h1 := (frM_spec D ω hω (p + ℓ)).1
      have hlt : ℓ * D + frM D ω (p + ℓ) + 2 < q * D := by
        have : (ℓ + 1) * D ≤ q * D := Nat.mul_le_mul_right D hℓ
        have : (ℓ + 1) * D = ℓ * D + D := by ring
        omega
      exact ⟨hlt, (mem_frI_iff D ω hω p q _ hlt).2 ⟨ℓ, hℓ, rfl⟩⟩
  rw [key, Set.InjOn.ncard_image]
  · rw [show Set.Iio q = ((Finset.range q : Finset ℕ) : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  · intro ℓ1 _ ℓ2 _ h
    simp only at h
    have h1 := (frM_spec D ω hω (p + ℓ1)).1
    have h2 := (frM_spec D ω hω (p + ℓ2)).1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (ℓ1 + 1) * D ≤ ℓ2 * D := Nat.mul_le_mul_right D hlt
      have : (ℓ1 + 1) * D = ℓ1 * D + D := by ring
      omega
    · have : (ℓ2 + 1) * D ≤ ℓ1 * D := Nat.mul_le_mul_right D hlt
      have : (ℓ2 + 1) * D = ℓ2 * D + D := by ring
      omega

open Classical in
/-- `W^n_k` is in bijection with the functions on its free positions. -/
noncomputable def wSetEquiv (D : ℕ) (ω : ℕ → Fin 3) (n k : ℕ) :
    wSet D ω n k ≃ (freePos D ω n k → Bool) where
  toFun u := fun i => u.1.getD i.1 true
  invFun t := ⟨List.ofFn (fun i : Fin k => if h : i.1 ∈ freePos D ω n k then t ⟨i.1, h⟩ else true),
    by simp, fun i hi hnot => by
      simp only [List.getElem_ofFn]
      rw [dif_neg]
      rintro ⟨_, h2⟩
      exact hnot h2⟩
  left_inv u := by
    obtain ⟨u, hlen, hu⟩ := u
    apply Subtype.ext
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      split_ifs with h
      · rw [List.getD_eq_getElem _ _ h2]
      · have hi : i < k := by simpa using h1
        symm
        apply hu i h2
        intro hm
        exact h ⟨hi, hm⟩
  right_inv t := by
    funext ⟨i, hi⟩
    show (List.ofFn _).getD i true = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi.1)]
    simp only [List.getElem_ofFn]
    rw [dif_pos hi]

theorem ncard_wSet (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (n k : ℕ) (hn : D ∣ n)
    (hk : D ∣ k) : (wSet D ω n k).ncard = 2 ^ (k / D) := by
  have hD : 0 < D := by have := (frM_spec D ω hω 0).1; omega
  obtain ⟨p, rfl⟩ := hn
  obtain ⟨q, rfl⟩ := hk
  have hfin : (freePos D ω (D * p) (D * q)).Finite :=
    (Set.finite_lt_nat (D * q)).subset fun i hi => hi.1
  have := hfin.to_subtype
  rw [Set.ncard_def, Set.encard, ENat.card_congr (wSetEquiv D ω (D * p) (D * q))]
  rw [ENat.card_eq_coe_natCard, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool]
  · have h := ncard_freePos D ω hω p q
    rw [mul_comm p D, mul_comm q D] at h
    simp only [ENat.toNat_natCast]
    rw [Nat.card_coe_set_eq, h, Nat.mul_div_cancel_left _ hD]

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

theorem shiftRay_shiftRay (x : Ray) (m n : ℕ) : shiftRay (shiftRay x m) n = shiftRay x (n + m) := by
  funext i; simp [shiftRay]; congr 1; omega

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

theorem length_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) (v : List Bool)
    (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 := by
  obtain ⟨u, ⟨hu, -⟩, rfl⟩ := hv
  simp [hu]
  omega

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

theorem ray_smul_mul (g h : BinaryTreeAut) (x : Ray) : x <• (g * h) = (x <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

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

theorem take_succ_eq (v : List Bool) (t : ℕ) (ht : t < v.length) :
    v.take (t + 1) = v.take t ++ [v[t]] := by
  rw [List.take_succ, List.getElem?_eq_getElem ht]
  rfl

end ConstrH

end ErschlerZheng
end

section
/-!
# The maximal displacements (Erschler–Zheng p. 45)

On the levels of `𝔉_{j,n}` made of `g̃^v_j`: Lemma 7.16, with `|𝔰^{j+1}x ∧ 𝔰v| ⩽ |v| - 1 ⩽
2k_n + 2D - 1`. On the levels `{g_j}`: Lemma 7.5 at level `j`, the sections of `g_j` there having
word length `2`. The product `θ_n(ε, γ)`: the triangle inequality along the intermediate points
(`d_𝒮` is a difference of Gray codes on the orbit, A9) and `Σ_{i ⩽ n} 2^{i+C} < 2^{n+C+1}`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrDisp

open ConstrW ConstrH

theorem cofinal_of_orbit (ω : ℕ → Fin 3) (x : Ray) (hx : x ∈ orbitOne ω) : IsCofinal x := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have : x ∈ rightOrbit (grigorchuk ω) oneRay := hx
  rw [(hA2.2.1 ω oneRay).1] at this
  exact this

theorem orbit_smul (ω : ℕ → Fin 3) (x : Ray) (hx : x ∈ orbitOne ω) (g : BinaryTreeAut)
    (hg : g ∈ grigorchuk ω) : x <• g ∈ orbitOne ω := by
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨k * g, Subgroup.mul_mem _ hk hg, ?_⟩
  rw [MulOpposite.op_mul, mul_smul]

theorem dist_triangle (ω : ℕ → Fin 3) (x y z : Ray) (hx : IsCofinal x) (hy : IsCofinal y)
    (hz : IsCofinal z) : schreierDist ω x z ≤ schreierDist ω x y + schreierDist ω y z := by
  have h1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x z hx hz
  have h2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x y hx hy
  have h3 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω y z hy hz
  have : (schreierDist ω x z : ℤ) ≤ schreierDist ω x y + schreierDist ω y z := by
    rw [h1, h2, h3]
    exact abs_sub_le _ _ _
  exact_mod_cast this

theorem dist_self (ω : ℕ → Fin 3) (x : Ray) (hx : IsCofinal x) : schreierDist ω x x = 0 := by
  have h := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x x hx hx
  simp at h
  exact_mod_cast h

theorem wordLength_le_of_list (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    wordLength (gens ω) l.prod ≤ l.length :=
  Nat.sInf_le ⟨l, le_rfl, fun s hs => Or.inl (hl s hs), rfl⟩

end ConstrDisp

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

/-! ### Exchanging the letters `1` and `2` -/

/-! ### Generators that differ -/

/-! ### The milestone -/

theorem seq_good (ω : ℕ → Fin 3) (n : ℕ) :
    Good (evalWord ω n [.a, if ω (n - 1) = 2 then .c else .b]) n (seqG ω n) := by
  have := good_zfold ω n _ (chi_seqPair ω n) n 0 (by omega)
  rw [evalFree_seqPair] at this
  rw [seqG_eq]
  exact this

theorem levelStab_good (ω : ℕ → Fin 3) (n : ℕ) :
    seqG ω n ∈ levelStab (grigorchuk ω) n := by
  refine ⟨?_, fun v hv => (seq_good ω n v hv).1⟩
  rw [seqG_eq]; exact evalFree_zero_mem ω _

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

theorem sSib_succ (ω : ℕ → Fin 3) (x : Bool) (v' : List Bool) (i : ℕ) :
    sSib ω (x :: v') (i + 1) = sSib (shiftSeq ω 1) v' i := by
  unfold sSib
  simp only [List.getD_cons_succ]
  rw [shiftSeq_shiftSeq]
  rfl

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

theorem qElt_spec : ∀ (v : List Bool) (ω : ℕ → Fin 3),
    (∀ i (h : i + 1 < v.length), v[i] = false → v[i + 1] = true) →
    (∀ i (h : i + 1 < v.length), v[i + 1] = false → letterValue (ω i) .b = true) →
    v <• qElt ω v = v ∧
      (∀ i (hi : i < v.length), sec (qElt ω v) (v.take i ++ [!v[i]]) = sSib ω v i) ∧
      sec (qElt ω v) v = gen (shiftSeq ω v.length) .c := by
  intro v
  induction v with
  | nil =>
    intro ω _ _
    refine ⟨nil_smul _, fun i hi => absurd hi (by simp), ?_⟩
    simp [qElt, kProd, sec_nil, shiftSeq_zero]
  | cons x v' ih =>
    intro ω H1 H2
    have H1' : ∀ i (h : i + 1 < v'.length), v'[i] = false → v'[i + 1] = true := by
      intro i h hf
      exact H1 (i + 1) (by simp; omega) hf
    have H2' : ∀ i (h : i + 1 < v'.length), v'[i + 1] = false →
        letterValue ((shiftSeq ω 1) i) .b = true := by
      intro i h hf
      exact H2 (i + 1) (by simp; omega) hf
    obtain ⟨ih1, ih2, ih3⟩ := ih (shiftSeq ω 1) H1' H2'
    have hq := qElt_cons ω x v'
      (by
        rintro rfl hh
        cases v' with
        | nil => simp at hh
        | cons y v'' =>
          simp at hh
          have := H1 0 (by simp) rfl
          simp [hh] at this)
      (by
        rintro rfl hh
        cases v' with
        | nil => simp at hh
        | cons y v'' =>
          simp at hh
          exact H2 0 (by simp) (by simp [hh]))
    have hsec : sec (qElt ω (x :: v')) [x] = qElt (shiftSeq ω 1) v' := by
      rw [hq]; cases x <;> simp [(dec_pairElt _ _).2.1, (dec_pairElt _ _).2.2]
    have hswap : rootSwap (qElt ω (x :: v')) = false := by
      rw [hq]; cases x <;> simp [(dec_pairElt _ _).1]
    refine ⟨?_, ?_, ?_⟩
    · rw [cons_smul, hswap, hsec, ih1]; simp
    · intro i hi
      cases i with
      | zero =>
        simp only [List.take_zero, List.nil_append, List.getElem_cons_zero]
        rw [hq]
        cases x
        · simp [(dec_pairElt _ _).2.2, sSib]
        · simp [(dec_pairElt _ _).2.1]
      | succ i =>
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
        rw [sec_cons, hsec, ih2 i (by simpa using hi), sSib_succ]
    · rw [sec_cons, hsec, ih3, shiftSeq_shiftSeq]
      simp [Nat.add_comm]

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

end ConstrFact714

end ErschlerZheng
end

section
/-!
# (7.7): the index set of `𝔉_{j,n}`, injectivity of `v ↦ g̃^v_j`, and `|𝔉_{j,n}|` (p. 40)

Injectivity: the section of `g̃^v_j` at `1^j` is `a𝔠^v_j`, and `v ↦ 𝔠^v_j` is injective: where two
words first differ, one element has the path section `qElt` (no root swap, `≠ 1`) and the other a
sibling section (`1`, or one that swaps level 1). The count: the prefix `1^{n-j+D}` fixes the first
`n - j + j̄` digits of `u ∈ W^{j+D-j̄}_{2k_n}`, a multiple of `D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrF8

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714

/-! ### Clause 1 -/

/-! ### Injectivity of `v ↦ 𝔠^v_j` -/

/-! ### The section of `g̃^v_j` at `1^j` -/

/-! ### The count -/

theorem prefix_append_iff (L a : ℕ) (u w : List Bool) (hL : a ≤ L) (hu : L - a ≤ u.length) :
    List.replicate L true <+: List.replicate a true ++ u ++ w ↔
      List.replicate (L - a) true <+: u := by
  have e : List.replicate L true = List.replicate a true ++ List.replicate (L - a) true := by
    rw [← List.replicate_add]; congr 1; omega
  rw [e, List.append_assoc, List.prefix_append_right_inj]
  constructor
  · intro h
    rw [List.prefix_iff_eq_take, List.length_replicate,
      List.take_append_of_le_length (by simpa using hu)] at h
    rw [h]
    exact List.take_prefix _ _
  · intro h
    exact h.trans (List.prefix_append u w)

theorem wSet_prefix (D : ℕ) (ω : ℕ → Fin 3) (N K L : ℕ) (hLK : L ≤ K) :
    {u | u ∈ wSet D ω N K ∧ List.replicate L true <+: u} =
      (List.replicate L true ++ ·) '' wSet D ω (N + L) (K - L) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨hlen, hu⟩, hpre⟩
    obtain ⟨u', rfl⟩ := hpre
    refine ⟨u', ⟨by simp at hlen; omega, fun i hi hnot => ?_⟩, rfl⟩
    have := hu (L + i) (by simp; omega) (by
      rw [show N + (L + i + 1) = N + L + (i + 1) by omega]; exact hnot)
    rw [List.getElem_append_right (by simp)] at this
    simpa using this
  · rintro ⟨u', ⟨hlen, hu⟩, rfl⟩
    refine ⟨⟨by simp; omega, fun i hi hnot => ?_⟩, List.prefix_append _ _⟩
    by_cases h : i < L
    · rw [List.getElem_append_left (by simpa using h)]; simp
    · rw [List.getElem_append_right (by simp; omega)]
      apply hu
      rw [show N + L + (i - (List.replicate L true).length + 1) = N + (i + 1) by simp; omega]
      exact hnot

end ConstrF8

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
/-!
# Lemma 7.16: displacement by `g̃^v_j` (Erschler–Zheng p. 44)

`p = n - j + D`. Every `v` in the index set of `𝔉_{j,n}` begins with `1^{p+2}`: `j + p + 1 = n + D + 1`
and `n + D + 2` are `≡ 1, 2 (mod D)`, never in `I_ω`. At the vertex `x_1…x_j` the sections of
`(g̃, g_j)` are `(a𝔠, ac)` or `(𝔠a, ca)`; let `w = 𝔰^j x` (resp. `(𝔰^j x)·a`).
If `|𝔰^{j+1}x ∧ 𝔰v| < p`, `w` leaves `1^∞` at depth `⩽ p + 1`, where `𝔠` and `c` have the same
sections, so `x·g̃ = x·g_j` and Lemma 7.5 at level `j` gives `2^j·3`. Otherwise Lemma 7.5 at the
level where `w` leaves `v` (a section `1`, `a` or `bab`) or at `v` itself (`c`).
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrLemma716

open GrigBasic RayBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714 ConstrF8 ConstrRemark78

/-! ### Word lengths -/

theorem wordLength_le_of_list (ω : ℕ → Fin 3) (l : List BinaryTreeAut) (hl : ∀ s ∈ l, s ∈ gens ω) :
    wordLength (gens ω) l.prod ≤ l.length :=
  Nat.sInf_le ⟨l, le_rfl, fun s hs => Or.inl (hl s hs), rfl⟩

theorem grigA_mem_gens (ω : ℕ → Fin 3) : grigA ∈ gens ω := by simp [gens]

theorem gen_mem_gens (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ gens ω := by
  cases γ <;> simp [gens]

theorem wordLength_one (ω : ℕ → Fin 3) : wordLength (gens ω) 1 = 0 := by
  have := wordLength_le_of_list ω [] (by simp)
  simpa using this

theorem wordLength_sSib (ω : ℕ → Fin 3) (v : List Bool) (i : ℕ) :
    wordLength (gens (shiftSeq ω (i + 1))) (sSib ω v i) ≤ 3 := by
  unfold sSib
  have hb := gen_mem_gens (shiftSeq ω (i + 1)) .b
  have ha := grigA_mem_gens (shiftSeq ω (i + 1))
  unfold letterElt
  split_ifs
  · have e : gen (shiftSeq ω (i + 1)) .b * grigA * grigA * grigA * gen (shiftSeq ω (i + 1)) .b =
        [gen (shiftSeq ω (i + 1)) .b, grigA, gen (shiftSeq ω (i + 1)) .b].prod := by
      simp [mul_assoc, grigA_mul_grigA_mul]
    rw [e]
    exact (wordLength_le_of_list _ _ (by simp [hb, ha])).trans (by simp)
  · have e : gen (shiftSeq ω (i + 1)) .b * grigA * 1 * grigA * gen (shiftSeq ω (i + 1)) .b = 1 := by
      simp [mul_assoc, grigA_mul_grigA_mul, gen_mul_self]
    rw [e, wordLength_one]; omega
  · have := wordLength_le_of_list (shiftSeq ω (i + 1)) [grigA] (by simp [ha])
    simp at this; omega
  · rw [wordLength_one]; omega

/-! ### Common prefixes -/

theorem takeWhile_exact {α : Type*} (P : α → Bool) :
    ∀ (L : List α) (h : (L.takeWhile P).length < L.length),
      P (L[(L.takeWhile P).length]'h) = false ∧
        ∀ t (ht : t < (L.takeWhile P).length), P (L[t]'(by omega)) = true := by
  intro L
  induction L with
  | nil => intro h; simp at h
  | cons a L ih =>
    intro h
    by_cases ha : P a = true
    · have e : (a :: L).takeWhile P = a :: L.takeWhile P := by rw [List.takeWhile_cons, if_pos ha]
      have h' : (L.takeWhile P).length < L.length := by
        rw [e] at h; simpa using h
      obtain ⟨h1, h2⟩ := ih h'
      simp only [e, List.length_cons, List.getElem_cons_succ]
      refine ⟨h1, fun t ht => ?_⟩
      cases t with
      | zero => simpa using ha
      | succ t => simpa using h2 t (by omega)
    · have e : (a :: L).takeWhile P = [] := by
        rw [List.takeWhile_cons, if_neg ha]
      simp only [e, List.length_nil, List.getElem_cons_zero]
      exact ⟨by simpa using ha, fun t ht => by simp at ht⟩

theorem commonPrefixLength_spec (l : List Bool) (y : Ray) :
    commonPrefixLength l y ≤ l.length ∧
      (∀ t < commonPrefixLength l y, ∀ ht : t < l.length, l[t] = y t) ∧
      (∀ ht : commonPrefixLength l y < l.length, l[commonPrefixLength l y] ≠ y (commonPrefixLength l y)) := by
  unfold commonPrefixLength
  set L := l.zip (rayPrefix y l.length)
  have hL : L.length = l.length := by simp [L, length_rayPrefix]
  have hle : (L.takeWhile fun p => p.1 = p.2).length ≤ l.length := by
    have := (List.takeWhile_prefix (p := fun p : Bool × Bool => decide (p.1 = p.2)) (l := L)).length_le
    rw [hL] at this; exact this
  refine ⟨hle, fun t ht htl => ?_, fun ht => ?_⟩
  · by_cases hlt : (L.takeWhile fun p => p.1 = p.2).length < L.length
    · have := (takeWhile_exact _ L hlt).2 t ht
      simpa [L, getElem_rayPrefix] using this
    · have heq : L.takeWhile (fun p => p.1 = p.2) = L := by
        apply List.takeWhile_eq_self_iff.mpr
        intro p hp
        have : (L.takeWhile fun p => p.1 = p.2).length = L.length := by
          have := (List.takeWhile_prefix (p := fun p : Bool × Bool => decide (p.1 = p.2))
            (l := L)).length_le
          omega
        exact List.takeWhile_eq_self_iff.mp
          (List.IsPrefix.eq_of_length (List.takeWhile_prefix _) this) p hp
      have hmem : L[t]'(by omega) ∈ L.takeWhile (fun p => p.1 = p.2) := by
        rw [heq]; exact List.getElem_mem _
      have := List.mem_takeWhile_imp hmem
      simpa [L, getElem_rayPrefix] using this
  · have hlt : (L.takeWhile fun p => p.1 = p.2).length < L.length := by omega
    have := (takeWhile_exact _ L hlt).1
    simpa [L, getElem_rayPrefix] using this

/-! ### `v` begins with `1^{p+2}` -/

theorem prefix_two_more (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (n : ℕ) (hn : D ∣ n)
    (j : ℕ) (hjn' : j ≤ n) (k : ℕ) (hk : D ∣ k) (v : List Bool) (hv : v ∈ vSet D ω j k)
    (t : ℕ) (ht : t < v.length) (htp : t = n - j + D ∨ t = n - j + D + 1) : v[t] = true := by
  by_contra hne
  have hf : v[t] = false := by simpa using hne
  obtain ⟨-, ⟨ℓ, hℓ⟩⟩ := getElem_of_mem_vSet D ω hω j k hk v hv t ht hf
  have hm := (frM_spec D ω hω ℓ).1
  obtain ⟨q, rfl⟩ := hn
  have e : j + (t + 1) = D * q + D + 1 ∨ j + (t + 1) = D * q + D + 2 := by omega
  rcases Nat.lt_or_ge ℓ (q + 1) with h | h
  · have : (ℓ + 1) * D ≤ (q + 1) * D := Nat.mul_le_mul_right D h
    have : (ℓ + 1) * D = ℓ * D + D := by ring
    have : (q + 1) * D = D * q + D := by ring
    omega
  · have : (q + 1) * D ≤ ℓ * D := Nat.mul_le_mul_right D h
    have : (q + 1) * D = D * q + D := by ring
    omega

/-! ### `qElt` on a ray leaving the path -/

theorem qElt_smul_sibling (ω : ℕ → Fin 3) (v : List Bool) (hv1 : H1 v) (hv2 : H2 ω v) (i : ℕ)
    (hi : i < v.length) (T : Ray) :
    prepend (v.take i ++ [!v[i]]) T <• qElt ω v = prepend (v.take i ++ [!v[i]]) (T <• sSib ω v i) := by
  obtain ⟨s1, s2, -⟩ := qElt_spec v ω hv1 hv2
  have hfix := take_smul_of_smul_eq _ v s1
  have hsib : (v.take i ++ [!v[i]]) <• qElt ω v = v.take i ++ [!v[i]] := by
    apply sibling_fixed _ _ v[i] (hfix i)
    rw [← take_succ_eq v i hi]; exact hfix _
  rw [prepend_smul, hsib, s2 i hi]

theorem sSib_congr (ω : ℕ → Fin 3) (v v' : List Bool) (i : ℕ)
    (h0 : v.getD i true = v'.getD i true) (h1 : v.getD (i + 1) true = v'.getD (i + 1) true) :
    sSib ω v i = sSib ω v' i := by
  unfold sSib; rw [h0, h1]

/-! ### The milestone -/

end ConstrLemma716

end ErschlerZheng
end

section
/-!
# A12: Lemma 7.5, p. 35

`g_v ∈ G_{𝔰ⁿω}` for `|v| = n` (closure induction, sections of products by A4), and
`d(x, x·g) ⩽ 2ⁿ d(𝔰ⁿx, (𝔰ⁿx)·g_v) + 2ⁿ - 1` (A11, since `𝔰ⁿ(x·g) = (𝔰ⁿx)·g_v`), where the last
distance does not depend on the string (A9) and is at most the word length of `g_v`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace Lemma75Dev

open GrigBasic RayBasic SchreierDev

/-- Sections of a product, from (7.17) (A4). -/
theorem sec_mul' (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  have := sec_list_prod [g, h] v
  simpa using this

theorem sec_inv' (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul' g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem shiftSeq_add (ω : ℕ → Fin 3) (m : ℕ) : shiftSeq (shiftSeq ω 1) m = shiftSeq ω (m + 1) :=
  shiftSeq_shiftSeq ω 1 m

theorem letterElt_mem (ω : ℕ → Fin 3) (i : Fin 3) (γ : BCD) : letterElt i γ ∈ grigorchuk ω := by
  unfold letterElt
  split_ifs
  · exact Subgroup.subset_closure (by simp [gens])
  · exact Subgroup.one_mem _

theorem sec_gen_mem (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    sec (gen ω γ) v ∈ grigorchuk (shiftSeq ω v.length) := by
  induction v generalizing ω with
  | nil =>
    rw [sec_nil, List.length_nil, shiftSeq_zero]
    exact Subgroup.subset_closure (gen_mem_gens' ω γ)
  | cons b u ih =>
    rw [sec_cons]
    cases b
    · rw [sec_gen_false]
      cases u with
      | nil => rw [sec_nil]; exact letterElt_mem _ _ _
      | cons c u' =>
        unfold letterElt
        split_ifs
        · rw [sec_grigA_cons]; exact Subgroup.one_mem _
        · rw [sec_one]; exact Subgroup.one_mem _
    · rw [sec_gen_true]
      have := ih (shiftSeq ω 1)
      rw [shiftSeq_add] at this
      rwa [List.length_cons]
where
  gen_mem_gens' (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ ∈ gens ω := by cases γ <;> simp [gens]

theorem sec_grigA_mem (ω : ℕ → Fin 3) (v : List Bool) :
    sec grigA v ∈ grigorchuk (shiftSeq ω v.length) := by
  cases v with
  | nil => rw [sec_nil, List.length_nil, shiftSeq_zero]; exact Subgroup.subset_closure (by simp [gens])
  | cons b u => rw [sec_grigA_cons]; exact Subgroup.one_mem _

theorem sec_mem (ω : ℕ → Fin 3) (g : BinaryTreeAut) (hg : g ∈ grigorchuk ω) :
    ∀ v : List Bool, sec g v ∈ grigorchuk (shiftSeq ω v.length) := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    intro v
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact sec_grigA_mem ω v
    all_goals exact sec_gen_mem ω _ v
  | one => intro v; rw [sec_one]; exact Subgroup.one_mem _
  | mul g h _ _ ihg ihh =>
    intro v
    rw [sec_mul']
    refine Subgroup.mul_mem _ (ihg v) ?_
    have := ihh (v <• g)
    rwa [length_vertex_smul] at this
  | inv g _ ihg =>
    intro v
    rw [sec_inv']
    refine Subgroup.inv_mem _ ?_
    have := ihg (v <• g⁻¹)
    rwa [length_vertex_smul] at this

theorem isCofinal_smul (ω : ℕ → Fin 3) (g : BinaryTreeAut) (hg : g ∈ grigorchuk ω) :
    ∀ x, IsCofinal x → IsCofinal (x <• g) := by
  suffices H : (∀ x, IsCofinal x → IsCofinal (x <• g)) ∧ ∀ x, IsCofinal x → IsCofinal (x <• g⁻¹) from
    H.1
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    have key : ∀ x, IsCofinal x → IsCofinal (x <• s) := by
      intro x hx
      obtain ⟨N, hN⟩ := (isCofinal_iff x).mp hx
      exact (isCofinal_iff _).mpr ⟨N + 1, allOnesFrom_smul_gens ω hs hN⟩
    refine ⟨key, ?_⟩
    rw [gens_involutive ω hs]
    exact key
  | one => exact ⟨fun x hx => by rwa [one_smul_ray], fun x hx => by rwa [inv_one, one_smul_ray]⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [MulOpposite.op_mul, mul_smul]; exact ihh.1 _ (ihg.1 x hx)
    · rw [mul_inv_rev, MulOpposite.op_mul, mul_smul]; exact ihg.2 _ (ihh.2 x hx)
  | inv g _ ihg => exact ⟨ihg.2, by rw [inv_inv]; exact ihg.1⟩

/-- The subgroup generated by `S` is the union of the balls. -/
theorem exists_mem_wordBall {G : Type*} [Group G] (S : Set G) (g : G)
    (hg : g ∈ Subgroup.closure S) : ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, [], le_rfl, by simp, rfl⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    obtain ⟨n, l', hl', hls', rfl⟩ := ihh
    refine ⟨m + n, l ++ l', by simp; omega, ?_, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hls x h
    · exact hls' x h
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

theorem mem_wordBall_wordLength {G : Type*} [Group G] (S : Set G) (g : G)
    (hg : g ∈ Subgroup.closure S) : g ∈ Chou.wordBall S (wordLength S g) := by
  obtain ⟨n, hn⟩ := exists_mem_wordBall S g hg
  exact Nat.sInf_mem (s := {n | g ∈ Chou.wordBall S n}) ⟨n, hn⟩

end Lemma75Dev

end ErschlerZheng
end

section
/-!
# A sharper Lemma 7.16 (prover 8)

The proof of `ConstrLemma716.chk_schreierDist_smul_gTilde_le` (prover 2), stopped before its
last estimate: the displacement by `g̃^v_j` is at most `2^{j+3}`, or, where the effective ray
leaves `v` at index `t = m + 1` (`m = |𝔰v ∧ 𝔰^{j+1}x|`), at most `2^{j+t+1}(|s_t| + 1)` with
`s_t` the section of `𝔠` at the sibling (`sSib`), or, where it runs through `v`, at most
`2^{j+|v|+1}`. Lemma 7.17 (i) needs this form: `|s_t| = 0` at the free digits of `v`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace P8Core

open GrigBasic RayBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714 ConstrF8 ConstrRemark78 ConstrLemma716

open Lemma75Dev SchreierDev RayBasic GrigBasic in
/-- Lemma 7.5 with its strict form, `d(x, x·g) ⩽ 2^n |g|_{x_{<n}}| + 2^n - 1` (Fact 7.4). -/
theorem strict75 (ω : ℕ → Fin 3) (g : Garrido.BinaryTreeAut) (hg : g ∈ grigorchuk ω) (n : ℕ)
    (x : Ray) (hx : IsCofinal x) :
    schreierDist ω x (x <• g) ≤
      2 ^ n * wordLength (gens (shiftSeq ω n)) (sec g (rayPrefix x n)) + 2 ^ n - 1 := by
  have hmem : sec g (rayPrefix x n) ∈ grigorchuk (shiftSeq ω n) := by
    have := sec_mem ω g hg (rayPrefix x n)
    rwa [length_rayPrefix] at this
  set h := sec g (rayPrefix x n)
  have hxg := isCofinal_smul ω g hg x hx
  have hA11 := schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal ω x (x <• g)
    hx hxg n
  rw [shiftRay_smul] at hA11
  set x' := shiftRay x n
  have hx' : IsCofinal x' := (Filter.tendsto_add_atTop_nat n).eventually hx
  have hx'h : IsCofinal (x' <• h) := isCofinal_smul (shiftSeq ω n) h hmem x' hx'
  have hd : schreierDist ω x' (x' <• h) = schreierDist (shiftSeq ω n) x' (x' <• h) := by
    have e1 := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω x' (x' <• h) hx' hx'h
    have e2 := schreierDist_eq_abs_sub_grayCode_of_isCofinal (shiftSeq ω n) x' (x' <• h) hx' hx'h
    exact_mod_cast e1.trans e2.symm
  have hwl : schreierDist (shiftSeq ω n) x' (x' <• h) ≤ wordLength (gens (shiftSeq ω n)) h :=
    Nat.sInf_le ⟨h, mem_wordBall_wordLength _ h hmem, rfl⟩
  rw [hd] at hA11
  have := Nat.mul_le_mul_left (2 ^ n) hwl
  omega

theorem disp_core (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (v : List Bool)
    (hv : v ∈ vSet D ω j (2 * k n)) (hv' : n - j + D ≤ commonPrefixLength v oneRay) (x : Ray)
    (hx : x ∈ orbitOne ω)
    (G Gj : BinaryTreeAut) (hmem1 : G ∈ grigorchuk ω) (hmem2 : Gj ∈ grigorchuk ω)
    (f1 : rayPrefix x j <• G = rayPrefix x j) (f2 : rayPrefix x j <• Gj = rayPrefix x j)
    (hs : (sec G (rayPrefix x j) = grigA * cElt ω j v ∧
        sec Gj (rayPrefix x j) = grigA * gen (shiftSeq ω j) .c) ∨
      (sec G (rayPrefix x j) = grigA * (grigA * cElt ω j v) * grigA ∧
        sec Gj (rayPrefix x j) = grigA * (grigA * gen (shiftSeq ω j) .c) * grigA)) :
    schreierDist ω x (x <• G) ≤ 2 ^ (j + 3) ∨
    (∃ _h : commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 < v.length,
      schreierDist ω x (x <• G) <
        2 ^ (j + (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 + 1)) *
          (wordLength (gens (shiftSeq ω (j + (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 + 1))))
            (sSib (shiftSeq ω j) v (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1)) + 1)) ∨
    (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 = v.length ∧
      schreierDist ω x (x <• G) < 2 ^ (j + v.length + 1)) := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hkn := hk.2 n (by omega) hn
  have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
  have hkD : D ≤ k n := Nat.le_of_dvd hkn.1 hkn.2
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  obtain ⟨hv0, hv1, hv2⟩ := vSet_props D ω hω j _ h2k v hv
  have hlen := length_of_mem_vSet D ω j _ v hv
  set p := n - j + D with hp
  have hpl : p + 2 ≤ v.length := by rw [hlen]; omega
  obtain ⟨-, hpt⟩ := take_of_le_commonPrefixLength v p hv'
  -- `v` begins with `1^{p+2}`
  have hones : ∀ t (ht : t < p + 2), v[t]'(by omega) = true := by
    intro t ht
    by_cases htp : t < p
    · have := congrArg (fun l : List Bool => l[t]?) hpt
      simp only [List.getElem?_take, htp, if_true, List.getElem?_replicate] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    · exact prefix_two_more D ω hω n hn j hjn' _ h2k v hv t (by omega) (by omega)
  -- cofinality of `x`
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hxc : IsCofinal x := by
    have : x ∈ rightOrbit (grigorchuk ω) oneRay := hx
    rw [(hA2.2.1 ω oneRay).1] at this
    exact this
  set u1 := rayPrefix x j
  set 𝔠 := cElt ω j v
  have hq : 𝔠 = qElt (shiftSeq ω j) v := cElt_eq_qElt ω j v hv0
  set y' := shiftRay x j
  set y := shiftRay x (j + 1)
  set m := commonPrefixLength (v.drop 1) y
  obtain ⟨hm1, hm2, hm3⟩ := commonPrefixLength_spec (v.drop 1) y
  have hxsplit : x = prepend u1 y' := (prepend_rayPrefix_shiftRay x j).symm
  have hy'y : shiftRay y' 1 = y := by rw [shiftRay_shiftRay, Nat.add_comm]
  -- the two candidate rays `w`
  have hS : ∀ g S, u1 <• g = u1 → sec g u1 = S → x <• g = prepend u1 (y' <• S) := by
    intro g S h1 h2
    conv_lhs => rw [hxsplit]
    rw [prepend_smul, h1, h2]
  -- A12 at a level `L`
  have hA12 : ∀ (g : BinaryTreeAut), g ∈ grigorchuk ω → ∀ L,
      schreierDist ω x (x <• g) ≤
        2 ^ L * (wordLength (gens (shiftSeq ω L)) (sec g (rayPrefix x L)) + 1) :=
    fun g hg L => (sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal ω g hg L x hxc).2
  have hA12s : ∀ (g : BinaryTreeAut), g ∈ grigorchuk ω → ∀ L,
      schreierDist ω x (x <• g) ≤
        2 ^ L * wordLength (gens (shiftSeq ω L)) (sec g (rayPrefix x L)) + 2 ^ L - 1 :=
    fun g hg L => strict75 ω g hg L x hxc
  have hsecA : ∀ u : List Bool, u ≠ [] → sec grigA u = 1 := by
    intro u hu
    obtain ⟨b, u', rfl⟩ := List.exists_cons_of_ne_nil hu
    exact sec_grigA_cons b u'
  have hsplitL : ∀ i, sec (G) (rayPrefix x (j + (i + 1))) =
      sec (sec (G) u1) (rayPrefix y' (i + 1)) := by
    intro i; rw [rayPrefix_add, sec_append]
  have hgen : gen (shiftSeq ω j) .c = qElt (shiftSeq ω j) (List.replicate v.length true) :=
    (qElt_replicate _ _).symm
  obtain ⟨s1, s2, -⟩ := qElt_spec v (shiftSeq ω j) hv1 hv2
  have s3 : sec (qElt (shiftSeq ω j) v) v = gen (shiftSeq (shiftSeq ω j) v.length) .c := by
    rw [← hq, shiftSeq_shiftSeq, Nat.add_comm]
    exact (smul_cElt_eq_self_and_sec_cElt_eq D ω hω j (2 * k n) h2k v hv).2.2.2
  have hlS : ∀ i, wordLength (gens (shiftSeq ω (j + (i + 1)))) (sSib (shiftSeq ω j) v i) ≤ 3 := by
    intro i
    have := wordLength_sSib (shiftSeq ω j) v i
    rwa [shiftSeq_shiftSeq, Nat.add_comm (i + 1) j] at this
  have hdrop : ∀ t (ht : t + 1 < v.length),
      (v.drop 1)[t]'(by rw [List.length_drop]; omega) = v[t + 1] := by
    intro t ht
    rw [List.getElem_drop]; congr 1; omega
  -- the main argument, for the ray `w` that `𝔠` acts on
  have main : ∀ w : Ray, shiftRay w 1 = y →
      (w <• 𝔠 = w <• gen (shiftSeq ω j) .c → x <• G = x <• Gj) →
      (∀ i, sec (G) (rayPrefix x (j + (i + 1))) = sec 𝔠 (rayPrefix w (i + 1))) →
      (schreierDist ω x (x <• G) ≤ 2 ^ (j + 3) ∨
        (∃ _h : m + 1 < v.length, schreierDist ω x (x <• G) <
          2 ^ (j + (m + 1 + 1)) * (wordLength (gens (shiftSeq ω (j + (m + 1 + 1))))
            (sSib (shiftSeq ω j) v (m + 1)) + 1)) ∨
        (m + 1 = v.length ∧ schreierDist ω x (x <• G) < 2 ^ (j + v.length + 1))) := by
    intro w hw hact hsec
    have hwy : ∀ t, w (t + 1) = y t := by
      intro t; rw [← hw]; simp [shiftRay]
    have hydrop : ∀ t < m, ∀ ht : t + 1 < v.length, y t = v[t + 1] := by
      intro t htm ht
      rw [← hm2 t htm (by simp; omega)]
      simp
    have hw_split : w = prepend [w 0] y := by
      rw [← hw]; exact (prepend_rayPrefix_shiftRay w 1).symm.trans (by simp [rayPrefix])
    rcases le_or_gt p m with hpm | hmp
    · 
      by_cases hw0 : w 0 = false
      · have := hA12 _ hmem1 (j + (0 + 1))
        rw [hsec 0] at this
        have hr : rayPrefix w (0 + 1) = v.take 0 ++ [!v[0]'(by omega)] := by
          simp [rayPrefix, hw0, hones 0 (by omega)]
        rw [hr, hq, s2 0 (by omega)] at this
        have hl := hlS 0
        refine Or.inl (this.trans ?_)
        calc 2 ^ (j + (0 + 1)) * (wordLength (gens (shiftSeq ω (j + (0 + 1))))
              (sSib (shiftSeq ω j) v 0) + 1) ≤ 2 ^ (j + (0 + 1)) * 4 := by
              gcongr; omega
          _ = 2 ^ (j + (0 + 1) + 2) := by rw [pow_add 2 (j + (0 + 1)) 2]; norm_num
          _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · have hw0' : w 0 = true := by simpa using hw0
        by_cases hmv : m + 1 < v.length
        · -- `w` leaves `v` at depth `m + 2`
          have hneq : y m = !v[m + 1] := by
            have := hm3 (by rw [List.length_drop]; omega)
            rw [hdrop m hmv] at this
            revert this
            cases y m <;> cases v[m + 1] <;> simp
          have hr : rayPrefix w (m + 1 + 1) = v.take (m + 1) ++ [!v[m + 1]] := by
            apply List.ext_getElem
            · simp [length_rayPrefix]; omega
            · intro t h1 h2
              rw [getElem_rayPrefix]
              simp only [length_rayPrefix] at h1
              by_cases ht : t < m + 1
              · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
                cases t with
                | zero => rw [hw0', hones 0 (by omega)]
                | succ t => rw [hwy, hydrop t (by omega) (by omega)]
              · have : t = m + 1 := by omega
                subst this
                rw [List.getElem_append_right (by simp only [List.length_take]; omega)]
                simp only [List.length_take, min_eq_left (show m + 1 ≤ v.length by omega),
                  Nat.sub_self, List.getElem_cons_zero]
                rw [hwy, hneq]
          have := hA12s _ hmem1 (j + (m + 1 + 1))
          rw [hsec (m + 1), hr, hq, s2 (m + 1) hmv] at this
          refine Or.inr (Or.inl ⟨hmv, ?_⟩)
          have hp : 1 ≤ 2 ^ (j + (m + 1 + 1)) := Nat.one_le_two_pow
          rw [mul_add, mul_one]
          omega
        · -- `w` passes through `v`
          have hmv' : m + 1 = v.length := by rw [List.length_drop] at hm1; omega
          have hr : rayPrefix w v.length = v := by
            apply List.ext_getElem
            · simp [length_rayPrefix]
            · intro t h1 h2
              rw [getElem_rayPrefix]
              cases t with
              | zero => rw [hw0', hones 0 (by omega)]
              | succ t => rw [hwy, hydrop t (by omega) (by omega)]
          have := hA12s _ hmem1 (j + v.length)
          rw [← hmv', hsec m, hmv', hr, hq, s3, shiftSeq_shiftSeq,
            show v.length + j = j + v.length by omega] at this
          have hl : wordLength (gens (shiftSeq ω (j + v.length)))
              (gen (shiftSeq ω (j + v.length)) .c) ≤ 1 := by
            have := wordLength_le_of_list (shiftSeq ω (j + v.length))
              [gen (shiftSeq ω (j + v.length)) .c] (by simp [gen_mem_gens])
            simpa using this
          refine Or.inr (Or.inr ⟨hmv', ?_⟩)
          have hp : 1 ≤ 2 ^ (j + v.length) := Nat.one_le_two_pow
          have h2 := Nat.mul_le_mul_left (2 ^ (j + v.length)) hl
          rw [pow_succ]
          omega
    · 
      -- `w` leaves `1^∞` at depth `⩽ p + 1`, where `𝔠` and `c` agree
      have hmlt : m < (v.drop 1).length := by rw [List.length_drop]; omega
      have hym : y m = false := by
        have := hm3 hmlt
        rw [hdrop m (by omega), hones (m + 1) (by omega)] at this
        revert this; cases y m <;> simp
      have hagree : w <• 𝔠 = w <• gen (shiftSeq ω j) .c := by
        obtain ⟨i, T, hip, hwT⟩ : ∃ i T, i ≤ p ∧
            w = prepend (List.replicate i true ++ [false]) T := by
          by_cases hw0 : w 0 = false
          · exact ⟨0, y, by omega, by rw [hw_split, hw0]; rfl⟩
          · have hw0' : w 0 = true := by simpa using hw0
            refine ⟨m + 1, shiftRay y (m + 1), by omega, ?_⟩
            funext t
            unfold prepend
            split_ifs with ht
            · simp only [List.length_append, List.length_replicate, List.length_singleton] at ht
              by_cases ht' : t < m + 1
              · rw [List.getElem_append_left (by simpa using ht'), List.getElem_replicate]
                cases t with
                | zero => exact hw0'
                | succ t => rw [hwy, hydrop t (by omega) (by omega), hones (t + 1) (by omega)]
              · have : t = m + 1 := by omega
                subst this
                rw [List.getElem_append_right (by simp)]
                simp [hwy, hym]
            · simp only [List.length_append, List.length_replicate, List.length_singleton] at ht
              have ht1 : t = (t - 1) + 1 := by omega
              rw [ht1, hwy]
              simp only [shiftRay, List.length_append, List.length_replicate, List.length_singleton]
              congr 1; omega
        have hiv : i < v.length := by omega
        have htake : v.take i ++ [!v[i]] = List.replicate i true ++ [false] := by
          rw [hones i (by omega)]
          congr 1
          apply List.ext_getElem
          · simp; omega
          · intro t h1 h2
            simp only [List.getElem_take, List.getElem_replicate]
            exact hones t (by simp at h2; omega)
        have htake' : (List.replicate v.length true).take i ++
            [!(List.replicate v.length true)[i]'(by simp; omega)] =
              List.replicate i true ++ [false] := by
          simp [List.take_replicate, min_eq_left (le_of_lt hiv)]
        rw [hgen, hq, hwT, ← htake]
        conv_rhs => rw [htake, ← htake']
        rw [qElt_smul_sibling _ v hv1 hv2 i hiv,
          qElt_smul_sibling _ _ (H1_replicate _) (H2_replicate _ _) i (by simp; omega)]
        rw [htake', ← htake]
        rw [sSib_congr (shiftSeq ω j) v (List.replicate v.length true) i ?_ ?_]
        · rw [List.getD_eq_getElem _ _ hiv, hones i (by omega)]; simp
        · rw [List.getD_eq_getElem _ _ (by omega), hones (i + 1) (by omega)]
          rw [List.getD_eq_getElem _ _ (by simp; omega)]
          simp
      rw [hact hagree]
      have := hA12 _ hmem2 j
      refine Or.inl (this.trans (le_trans ?_ (Nat.pow_le_pow_right (by norm_num)
        (show j + 2 ≤ j + 3 by omega))))
      have hl : wordLength (gens (shiftSeq ω j)) (sec (Gj) u1) ≤ 2 := by
        have ha := grigA_mem_gens (shiftSeq ω j)
        have hc := gen_mem_gens (shiftSeq ω j) .c
        rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
        · have := wordLength_le_of_list (shiftSeq ω j) [grigA, gen (shiftSeq ω j) .c] (by simp [ha, hc])
          simpa using this
        · rw [grigA_mul_grigA_mul]
          have := wordLength_le_of_list (shiftSeq ω j) [gen (shiftSeq ω j) .c, grigA]
            (by simp [ha, hc])
          simpa using this
      calc 2 ^ j * (wordLength (gens (shiftSeq ω j)) (sec (Gj) u1) + 1) ≤ 2 ^ j * 4 := by
            gcongr; omega
        _ = 2 ^ (j + 2) := by rw [pow_add]; norm_num
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- sections `a𝔠`, `ac`: `w = (𝔰^j x)·a`
    refine main (y' <• grigA) ?_ ?_ ?_
    · rw [← hy'y, shiftRay_smul_one, sec_grigA, one_smul_ray]
    · intro hag
      rw [hS _ _ f1 h1, hS _ _ f2 h2, ray_smul_mul, ray_smul_mul, hag]
    · intro i
      rw [hsplitL, h1, sec_mul, hsecA _ (by
        intro h; have := congrArg List.length h; simp [length_rayPrefix] at this), one_mul,
        ← rayPrefix_smul]
  · -- sections `𝔠a`, `ca`: `w = 𝔰^j x`
    rw [grigA_mul_grigA_mul] at h1 h2
    refine main y' hy'y ?_ ?_
    · intro hag
      rw [hS _ _ f1 h1, hS _ _ f2 h2, ray_smul_mul, ray_smul_mul, hag]
    · intro i
      rw [hsplitL, h1, sec_mul, hsecA _ (by
        intro h; have := congrArg List.length h
        simp [length_vertex_smul, length_rayPrefix] at this), mul_one]


theorem disp (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (v : List Bool)
    (hv : v ∈ vSet D ω j (2 * k n)) (hv' : n - j + D ≤ commonPrefixLength v oneRay) (x : Ray)
    (hx : x ∈ orbitOne ω) :
    schreierDist ω x (x <• gTilde ω j v) ≤ 2 ^ (j + 3) ∨
    (∃ _h : commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 < v.length,
      schreierDist ω x (x <• gTilde ω j v) <
        2 ^ (j + (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 + 1)) *
          (wordLength (gens (shiftSeq ω (j + (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 + 1))))
            (sSib (shiftSeq ω j) v (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1)) + 1)) ∨
    (commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) + 1 = v.length ∧
      schreierDist ω x (x <• gTilde ω j v) < 2 ^ (j + v.length + 1)) := by
  have hkn := hk.2 n (by omega) hn
  have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
  -- `g̃` and `g_j` side by side at level `j`
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
  obtain ⟨f1, f2, hs⟩ := hgp (rayPrefix x j) (length_rayPrefix _ _)
  have hmem1 : gTilde ω j v ∈ grigorchuk ω := by rw [hg1]; exact evalFree_zero_mem ω _
  have hmem2 : seqG ω j ∈ grigorchuk ω := (levelStab_good ω j).1
  exact disp_core D ω hω k hk n hn j hj1 hj hjn hjn' v hv hv' x hx (gTilde ω j v) (seqG ω j)
    hmem1 hmem2 f1 f2 hs

/-! ### Lemma 7.17 (i) on the levels made of `g̃`'s -/

theorem mass_eq (F A : Set BinaryTreeAut) (hF : F.Finite) :
    mass (uniformMeasure F) A = ((F ∩ A).ncard : ℝ) * (F.ncard : ℝ)⁻¹ := by
  classical
  letI : Fintype ↥F := hF.fintype
  have hsupp : Function.support (A.indicator (uniformMeasure F)) ⊆ F := by
    intro g hg
    by_contra hgF
    apply hg
    simp [Set.indicator, uniformMeasure, hgF]
  have hcard : (F ∩ A).ncard = (Finset.univ.filter fun a : ↥F => (a : BinaryTreeAut) ∈ A).card := by
    rw [← Nat.card_coe_set_eq, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ F) (· ∈ A)).symm
  unfold mass
  rw [← tsum_subtype_eq_of_support_subset hsupp, tsum_fintype, hcard, Finset.card_filter,
    ← Nat.card_coe_set_eq]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : BinaryTreeAut) ∈ A
  · simp [Set.indicator, ha, uniformMeasure]
  · simp [Set.indicator, ha]

theorem wSet_finite (D : ℕ) (ω : ℕ → Fin 3) (N K : ℕ) : (wSet D ω N K).Finite :=
  (List.finite_length_eq Bool K).subset fun _ hu => hu.1

/-- Fixing the first `c` digits of `u ∈ W^N_K` leaves at most `2^{(K-c)/D}` choices. -/
theorem ncard_wSet_take_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (N K c : ℕ)
    (hN : D ∣ N) (hK : D ∣ K) (hc : D ∣ c) (hcK : c ≤ K) (π : List Bool) :
    {u | u ∈ wSet D ω N K ∧ u.take c = π}.ncard ≤ 2 ^ ((K - c) / D) := by
  rw [← ncard_wSet D ω hω (N + c) (K - c) (Nat.dvd_add hN hc) (Nat.dvd_sub hK hc)]
  refine Set.ncard_le_ncard_of_injOn (fun u => u.drop c) ?_ ?_ (wSet_finite D ω _ _)
  · rintro u ⟨⟨hlen, hu⟩, -⟩
    refine ⟨by simp [hlen], fun i hi hnot => ?_⟩
    rw [List.getElem_drop]
    exact hu (c + i) (by simp at hi; omega) (by
      rw [show N + (c + i + 1) = N + c + (i + 1) by omega]; exact hnot)
  · rintro u1 ⟨-, h1⟩ u2 ⟨-, h2⟩ h
    simp only at h
    rw [← List.take_append_drop c u1, ← List.take_append_drop c u2, h1, h2, h]

theorem forced_one (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j K : ℕ) (hK : D ∣ K)
    (t : ℕ) (hc : letterValue (ω (j + t)) .c = true) (v : List Bool) (hv : v ∈ vSet D ω j K)
    (ht : t < v.length) : v[t] = true := by
  by_contra h
  have hf : v[t] = false := by simpa using h
  obtain ⟨-, hI⟩ := getElem_of_mem_vSet D ω hω j K hK v hv t ht hf
  obtain ⟨-, -, -, h1⟩ := window_of_mem_frI D ω hω hI
  rw [show j + (t + 1) - 1 = j + t by omega] at h1
  rw [h1] at hc
  simp [letterValue, BCD.killedBy] at hc

theorem wl_sSib_zero (ω : ℕ → Fin 3) (v : List Bool) (t : ℕ) (G : ℕ → Fin 3)
    (hc : letterValue (ω t) .c = false) : wordLength (gens G) (sSib ω v t) = 0 := by
  have he : letterElt (ω t) .c = 1 := by simp [letterElt, hc]
  have : sSib ω v t = 1 := by
    unfold sSib
    rw [he]
    split_ifs
    · simp [grigA_mul_self, gen_mul_self, mul_assoc, grigA_mul_grigA_mul]
    · rfl
  rw [this, wordLength_one]

theorem wl_sSib_one (ω : ℕ → Fin 3) (v : List Bool) (t : ℕ) (G : ℕ → Fin 3)
    (hp : ¬(v.getD t true = true ∧ v.getD (t + 1) true = false)) :
    wordLength (gens G) (sSib ω v t) ≤ 1 := by
  unfold sSib
  rw [if_neg hp]
  unfold letterElt
  split_ifs
  · have := wordLength_le_of_list G [grigA] (by simp [grigA_mem_gens])
    simpa using this
  · rw [wordLength_one]; omega


/-- **Lemma 7.17 (i), the levels made of `g̃`'s, for `ℓ > n + 2D`.** -/
theorem core_one (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) :
    ∀ j, 1 ≤ j → n < j + k n → j ≤ n → ω (j - 1) = 2 →
      ∀ ℓ : ℕ, n + 2 * D < ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
        mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
          (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2) := by
  intro j hj1 hjk hjn hωj ℓ hℓ1 _hℓ2 x hx
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  have hkn := hk.2 n hn1 hn
  have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
  have hkD : D ≤ k n := Nat.le_of_dvd hkn.1 hkn.2
  have hjD : j % D < D := Nat.mod_lt _ (by omega)
  have hjj : j % D ≤ j := Nat.mod_le _ _
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  obtain ⟨hset, hinj, hcard⟩ := injOn_gTilde_and_ncard_fSet_eq D ω hω k hk n hn j hj1 hωj hjk hjn
  set V' := {v ∈ vSet D ω j (2 * k n) | n - j + D ≤ commonPrefixLength v oneRay} with hV'
  have hfs : fSet D ω k j n = gTilde ω j '' V' := by
    unfold fSet
    rw [if_pos ⟨hωj, hjk, hjn⟩]
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image, hV']
    constructor
    · rintro ⟨v, hv, hp, rfl⟩; exact ⟨v, ⟨hv, hp⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hp⟩, rfl⟩; exact ⟨v, hv, hp, rfl⟩
  set S : Set (List Bool) :=
    {v | v ∈ V' ∧ 2 ^ ℓ ≤ schreierDist ω x (x <• gTilde ω j v)} with hS
  have hSV : S ⊆ V' := fun v hv => hv.1
  have hFA : fSet D ω k j n ∩ {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} = gTilde ω j '' S := by
    rw [hfs]; ext g
    simp only [Set.mem_inter_iff, Set.mem_image, hS, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hd⟩; exact ⟨v, ⟨hv, hd⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hd⟩, rfl⟩; exact ⟨⟨v, hv, rfl⟩, hd⟩
  have hfin : (fSet D ω k j n).Finite := Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  rw [mass_eq _ _ hfin, hFA, (hinj.mono hSV).ncard_image, hcard]
  -- the effective ray
  set wst : ℕ → Bool := fun i => if i = 0 then true else shiftRay x (j + 1) (i - 1) with hwst
  -- a certificate for each bad index
  have cert : ∀ v ∈ S, ∃ τ, ℓ - j - 2 ≤ τ ∧ τ ≤ ℓ - j ∧
      (∀ i < τ, ∀ h : i < v.length, v[i] = wst i) ∧
      (τ < ℓ - j → ∃ h : τ < v.length, v[τ] ≠ wst τ ∧ letterValue (ω (j + τ)) .c = true ∧
        (τ + 2 = ℓ - j → ∃ h' : τ + 1 < v.length, v[τ + 1] = false)) ∧
      ℓ ≤ j + v.length := by
    rintro v ⟨⟨hv, hv'⟩, hd⟩
    have hlen := length_of_mem_vSet D ω j _ v hv
    obtain ⟨hv0, -, -⟩ := vSet_props D ω hω j _ h2k v hv
    have hv0' : v[0]'(by omega) = true := by
      rw [List.getD_eq_getElem _ _ (by omega)] at hv0; exact hv0
    set m := commonPrefixLength (v.drop 1) (shiftRay x (j + 1)) with hm
    obtain ⟨hm1, hm2, hm3⟩ := commonPrefixLength_spec (v.drop 1) (shiftRay x (j + 1))
    have hagree : ∀ i < m + 1, ∀ h : i < v.length, v[i] = wst i := by
      intro i hi h
      cases i with
      | zero => simpa [hwst] using hv0'
      | succ i =>
        have := hm2 i (by omega) (by rw [List.length_drop]; omega)
        rw [List.getElem_drop] at this
        simp only [hwst, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [← this]
        congr 1
        omega
    have hdis : ∀ h : m + 1 < v.length, v[m + 1] ≠ wst (m + 1) := by
      intro h
      have := hm3 (by rw [List.length_drop]; omega)
      rw [List.getElem_drop] at this
      simp only [hwst, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      have e : v[1 + m] = v[m + 1] := by congr 1; omega
      rw [e] at this
      exact this
    have hℓj : j + 6 < ℓ := by omega
    rcases disp D ω hω k hk n hn j hj1 hωj hjk hjn v hv hv' x hx with h1 | ⟨hmv, h2⟩ | ⟨hmv, h3⟩
    · exfalso
      have h := hd.trans h1
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
      omega
    · rw [← hm] at h2
      have hlt := lt_of_le_of_lt hd h2
      by_cases hlv : letterValue (ω (j + (m + 1))) .c = true
      · by_cases hpat : (v.getD (m + 1) true = true ∧ v.getD (m + 1 + 1) true = false)
        · have hl3 := wordLength_sSib (shiftSeq ω j) v (m + 1)
          rw [shiftSeq_shiftSeq, show m + 1 + 1 + j = j + (m + 1 + 1) by omega] at hl3
          have h4 : 2 ^ ℓ < 2 ^ (j + (m + 1 + 1) + 2) := by
            calc 2 ^ ℓ < _ := hlt
              _ ≤ 2 ^ (j + (m + 1 + 1)) * 4 := by gcongr; omega
              _ = 2 ^ (j + (m + 1 + 1) + 2) := by rw [pow_add 2 (j + (m + 1 + 1)) 2]; norm_num
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h4
          have hm2' : m + 1 + 1 < v.length := by
            by_contra hc
            have : v.getD (m + 1 + 1) true = true := by
              rw [List.getD_eq_default _ _ (by omega)]
            rw [this] at hpat; exact absurd hpat.2 (by simp)
          by_cases hτ : ℓ - j ≤ m + 1
          · exact ⟨ℓ - j, by omega, le_rfl, fun i hi h => hagree i (by omega) h,
              fun h => absurd h (lt_irrefl _), by omega⟩
          · refine ⟨m + 1, by omega, by omega, hagree, fun _ => ⟨hmv, hdis hmv, hlv, fun _ => ?_⟩,
              by omega⟩
            refine ⟨hm2', ?_⟩
            have := hpat.2
            rwa [List.getD_eq_getElem _ _ hm2'] at this
        · have hl1 := wl_sSib_one (shiftSeq ω j) v (m + 1) (shiftSeq ω (j + (m + 1 + 1))) hpat
          have h4 : 2 ^ ℓ < 2 ^ (j + (m + 1 + 1) + 1) := by
            calc 2 ^ ℓ < _ := hlt
              _ ≤ 2 ^ (j + (m + 1 + 1)) * 2 := by gcongr; omega
              _ = 2 ^ (j + (m + 1 + 1) + 1) := by rw [pow_succ]
          have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h4
          by_cases hτ : ℓ - j ≤ m + 1
          · exact ⟨ℓ - j, by omega, le_rfl, fun i hi h => hagree i (by omega) h,
              fun h => absurd h (lt_irrefl _), by omega⟩
          · exact ⟨m + 1, by omega, by omega, hagree,
              fun _ => ⟨hmv, hdis hmv, hlv, fun h => by omega⟩, by omega⟩
      · have hlv' : letterValue (shiftSeq ω j (m + 1)) .c = false := by
          simp only [shiftSeq]
          rw [show m + 1 + j = j + (m + 1) by omega]
          simpa using hlv
        have hl0 := wl_sSib_zero (shiftSeq ω j) v (m + 1) (shiftSeq ω (j + (m + 1 + 1))) hlv'
        rw [hl0, zero_add, mul_one] at hlt
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
        exact ⟨ℓ - j, by omega, le_rfl, fun i hi h => hagree i (by omega) h,
          fun h => absurd h (lt_irrefl _), by omega⟩
    · rw [← hm] at hmv
      have h := lt_of_le_of_lt hd h3
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
      exact ⟨ℓ - j, by omega, le_rfl, fun i hi h => hagree i (by omega) h,
        fun h => absurd h (lt_irrefl _), by omega⟩
  -- all bad indices share their first `ℓ - j` digits
  have key : ∀ (va vb : List Bool), va ∈ vSet D ω j (2 * k n) → vb ∈ vSet D ω j (2 * k n) →
      ∀ τa τb, τa < τb → τb ≤ ℓ - j → (∀ i < τb, ∀ h : i < vb.length, vb[i] = wst i) →
      (τa < ℓ - j → ∃ h : τa < va.length, va[τa] ≠ wst τa ∧
        letterValue (ω (j + τa)) .c = true ∧
        (τa + 2 = ℓ - j → ∃ h' : τa + 1 < va.length, va[τa + 1] = false)) → False := by
    intro va vb hva hvb τa τb hab hbL hb hc
    obtain ⟨h, hne, hlv, -⟩ := hc (by omega)
    have hla := length_of_mem_vSet D ω j _ va hva
    have hlb := length_of_mem_vSet D ω j _ vb hvb
    have e1 := forced_one D ω hω j _ h2k τa hlv va hva h
    have e2 := forced_one D ω hω j _ h2k τa hlv vb hvb (by omega)
    have e3 := hb τa hab (by omega)
    exact hne (e1.trans (e2.symm.trans e3))
  have pair : ∀ v1 ∈ S, ∀ v2 ∈ S, ∀ i < ℓ - j, ∀ (h1 : i < v1.length) (h2 : i < v2.length),
      v1[i] = v2[i] := by
    intro v1 hv1 v2 hv2 i hi h1 h2
    obtain ⟨τ1, a1, b1, c1, d1, -⟩ := cert v1 hv1
    obtain ⟨τ2, a2, b2, c2, d2, -⟩ := cert v2 hv2
    have hτ : τ1 = τ2 := by
      rcases lt_trichotomy τ1 τ2 with h | h | h
      · exact (key v1 v2 hv1.1.1 hv2.1.1 τ1 τ2 h b2 c2 d1).elim
      · exact h
      · exact (key v2 v1 hv2.1.1 hv1.1.1 τ2 τ1 h b1 c1 d2).elim
    subst hτ
    by_cases hiτ : i < τ1
    · rw [c1 i hiτ h1, c2 i hiτ h2]
    · have hτL : τ1 < ℓ - j := by omega
      obtain ⟨g1, -, l1, p1⟩ := d1 hτL
      obtain ⟨g2, -, -, p2⟩ := d2 hτL
      by_cases hie : i = τ1
      · subst hie
        rw [forced_one D ω hω j _ h2k i l1 v1 hv1.1.1 h1,
          forced_one D ω hω j _ h2k i l1 v2 hv2.1.1 h2]
      · have hτ2 : τ1 + 2 = ℓ - j := by omega
        obtain ⟨g1', f1⟩ := p1 hτ2
        obtain ⟨g2', f2⟩ := p2 hτ2
        have hi1 : i = τ1 + 1 := by omega
        subst hi1
        rw [f1, f2]
  -- the count
  rcases Set.eq_empty_or_nonempty S with hSe | ⟨v0, hv0⟩
  · rw [hSe, Set.ncard_empty]; simp only [Nat.cast_zero, zero_mul]; positivity
  obtain ⟨_, -, -, -, -, hℓv0⟩ := cert v0 hv0
  have hlv0 := length_of_mem_vSet D ω j _ v0 hv0.1.1
  set mm := frM D ω (ellIndex D (2 * k n) j) with hmm
  have hmm3 : mm + 3 ≤ D := (frM_spec D ω hω _).1
  set L0 := n - j + j % D with hL0
  have hL0D : D ∣ L0 := by
    have h1 : L0 + D * (j / D) = n := by have := Nat.div_add_mod j D; omega
    have : D ∣ L0 + D * (j / D) := by rw [h1]; exact hn
    exact (Nat.dvd_add_right (Dvd.intro _ rfl)).mp (by rwa [add_comm] at this)
  have hL0k : L0 ≤ 2 * k n := by
    obtain ⟨a, ha⟩ := hL0D
    obtain ⟨b, hb⟩ := hkn.2
    have : a < b + 1 := by
      by_contra hc
      have : D * (b + 1) ≤ D * a := Nat.mul_le_mul_left D (by omega)
      have : D * (b + 1) = D * b + D := by ring
      omega
    have : D * a ≤ D * b := Nat.mul_le_mul_left D (by omega)
    omega
  set K' := 2 * k n - L0 with hK'
  have hK'D : D ∣ K' := Nat.dvd_sub h2k hL0D
  obtain ⟨a, ha⟩ := hK'D
  set q := (ℓ - n) / D with hq
  have hq2 : 2 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le (by omega)]; omega
  set b := min (q - 1) a with hb
  set c := D * b with hc
  have hcK : c ≤ K' := by rw [ha, hc]; exact Nat.mul_le_mul_left D (min_le_right _ _)
  have hcq : c ≤ ℓ - n - D := by
    have : c ≤ D * (q - 1) := Nat.mul_le_mul_left D (min_le_left _ _)
    have h2 : D * (q - 1) = D * q - D := by rw [Nat.mul_sub_one]
    have h3 : D * q ≤ ℓ - n := by rw [hq]; exact Nat.mul_div_le _ _
    omega
  set P0 := n - j + D with hP0
  -- every `v ∈ V'` is `1^{P0} u' 1^{m+2} 0` with `u' ∈ W^{n+D}_{K'}`
  have hrep : ∀ v ∈ V', ∃ u' ∈ wSet D ω (n + D) K',
      v = List.replicate P0 true ++ u' ++ (List.replicate (mm + 2) true ++ [false]) := by
    intro v hv
    have hp : List.replicate (n - j + D) true <+: v := by
      have : v ∈ {v ∈ vSet D ω j (2 * k n) | List.replicate (n - j + D) true <+: v} := by
        rw [← hset]; exact hv
      exact this.2
    obtain ⟨u, hu, rfl⟩ := hv.1
    have hul : u.length = 2 * k n := hu.1
    rw [List.append_assoc] at hp
    rw [prefix_append_iff (n - j + D) (D - j % D) u _ (by omega) (by omega),
      show n - j + D - (D - j % D) = L0 by omega] at hp
    have hu' : u ∈ {u | u ∈ wSet D ω (j + D - j % D) (2 * k n) ∧
        List.replicate L0 true <+: u} := ⟨hu, hp⟩
    rw [wSet_prefix D ω _ _ L0 hL0k] at hu'
    obtain ⟨u', hu'w, rfl⟩ := hu'
    refine ⟨u', ?_, ?_⟩
    · rwa [show j + D - j % D + L0 = n + D by omega] at hu'w
    · have e : List.replicate P0 true =
          List.replicate (D - j % D) true ++ List.replicate L0 true := by
        rw [← List.replicate_add]; congr 1; omega
      rw [e, hmm]
      simp only [List.append_assoc]
  set φ : List Bool → List Bool := fun v => (v.drop P0).take K' with hφ
  have hφrep : ∀ u' : List Bool, u'.length = K' → ∀ T : List Bool,
      φ (List.replicate P0 true ++ u' ++ T) = u' := by
    intro u' hu' T
    simp only [hφ, List.append_assoc, List.drop_left' (List.length_replicate ..)]
    rw [List.take_left' hu']
  set T : Set (List Bool) := {v | v ∈ V' ∧ (φ v).take c = (φ v0).take c} with hT
  have hST : S ⊆ T := by
    intro v hv
    refine ⟨hv.1, ?_⟩
    have hlv := length_of_mem_vSet D ω j _ v hv.1.1
    apply List.ext_getElem
    · simp [hφ, hlv, hlv0, hmm]
    · intro i h1 h2
      simp only [hφ, List.getElem_take, List.getElem_drop]
      simp only [hφ, List.length_take, List.length_drop] at h1
      exact pair v hv v0 hv0 (P0 + i) (by omega) (by omega) (by omega)
  have hTfin : T.Finite := (List.finite_length_eq Bool (D - j % D + 2 * k n + mm + 3)).subset
    (fun v hv => length_of_mem_vSet D ω j _ v hv.1.1)
  have hcount : T.ncard ≤ 2 ^ (a - b) := by
    have hle := ncard_wSet_take_le D ω hω (n + D) K' c (Nat.dvd_add hn (dvd_refl D)) ⟨a, ha⟩
      ⟨b, hc⟩ hcK ((φ v0).take c)
    have e : (K' - c) / D = a - b := by
      rw [ha, hc, ← mul_tsub, Nat.mul_div_cancel_left _ (by omega)]
    rw [e] at hle
    refine le_trans (Set.ncard_le_ncard_of_injOn φ ?_ ?_
      ((wSet_finite D ω (n + D) K').subset fun u hu => hu.1)) hle
    · rintro v ⟨hv, hvt⟩
      obtain ⟨u', hu', rfl⟩ := hrep v hv
      refine ⟨?_, hvt⟩
      rw [hφrep u' hu'.1]; exact hu'
    · rintro v1 ⟨hv1, -⟩ v2 ⟨hv2, -⟩ h
      obtain ⟨u1, hu1, rfl⟩ := hrep v1 hv1
      obtain ⟨u2, hu2, rfl⟩ := hrep v2 hv2
      simp only [hφrep u1 hu1.1, hφrep u2 hu2.1] at h
      rw [h]
  have hSn : S.ncard ≤ 2 ^ (a - b) := (Set.ncard_le_ncard hST hTfin).trans hcount
  -- the arithmetic
  have hba : b ≤ a := min_le_right _ _
  have hfs' : (2 * k n - (n - j + j % D)) / D = a := by
    rw [show 2 * k n - (n - j + j % D) = K' from rfl, ha, Nat.mul_div_cancel_left _ (by omega)]
  rw [hfs']
  have hS' : (S.ncard : ℝ) ≤ (2 : ℝ) ^ (a - b) := by exact_mod_cast hSn
  have hpow : (2 : ℝ) ^ (a - b) * ((2 ^ a : ℕ) : ℝ)⁻¹ = (2 : ℝ) ^ (-(b : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat,
      pow_sub₀ _ (by norm_num) hba]
    field_simp
  have hexp : -(b : ℝ) ≤ -(((ℓ : ℝ) - n) / D) + 2 := by
    have hℓn : ((ℓ - n : ℕ) : ℝ) = (ℓ : ℝ) - n := by rw [Nat.cast_sub (by omega)]
    rcases min_cases (q - 1) a with ⟨hbq, -⟩ | ⟨hba', hlt⟩
    · -- `b = q - 1`
      have hlt : ℓ - n < D * (q + 1) := by
        rw [hq]
        have := Nat.div_add_mod (ℓ - n) D
        have := Nat.mod_lt (ℓ - n) (show 0 < D by omega)
        rw [mul_add, mul_one]; omega
      have hr : ((ℓ : ℝ) - n) ≤ D * (q + 1) := by
        rw [← hℓn]; exact_mod_cast hlt.le
      have hb' : (b : ℝ) = q - 1 := by rw [hb, hbq, Nat.cast_sub (by omega)]; simp
      rw [hb']
      have : ((ℓ : ℝ) - n) / D ≤ q + 1 := by rw [div_le_iff₀ hDr]; linarith
      linarith
    · -- `b = a`: then `ℓ - n ≤ K' + 2D`
      have hb' : (b : ℝ) = a := by rw [hb, hba']
      rw [hb']
      have hK2 : ℓ - n ≤ D * a + 2 * D := by
        rw [← ha]
        have h1 : ℓ ≤ j + (D - j % D + 2 * k n + mm + 3) := hlv0 ▸ hℓv0
        have h2 : K' = 2 * k n - L0 := rfl
        have h3 : L0 = n - j + j % D := rfl
        omega
      have hr : ((ℓ : ℝ) - n) ≤ D * a + 2 * D := by rw [← hℓn]; exact_mod_cast hK2
      have : ((ℓ : ℝ) - n) / D ≤ a + 2 := by rw [div_le_iff₀ hDr]; linarith
      linarith
  calc (S.ncard : ℝ) * ((2 ^ a : ℕ) : ℝ)⁻¹ ≤ (2 : ℝ) ^ (a - b) * ((2 ^ a : ℕ) : ℝ)⁻¹ := by
        gcongr
    _ = (2 : ℝ) ^ (-(b : ℝ)) := hpow
    _ ≤ (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end P8Core

end ErschlerZheng
end

section
/-!
# Lemma 7.17 (Erschler–Zheng p. 45): `chk_mass_uniformMeasure_fSet_le_and_card_fProd_le`

Prover 8. Part (ii) from part (i) by the union bound of p. 45 (`part2_of_part1`): if
`d(x, x·θ) ⩾ k_n 2^ℓ` with `ℓ > n + 3D`, some level `i` made of `g̃`'s, with `ε_i = 1`, moves its
intermediate point by at least `2^{ℓ-1}` (the levels `{g_i}` move by at most `2^{i+2}` (Lemma 7.5),
and `Σ_i 2^{i+2} < 2^{n+3}`); for fixed other coordinates, (i) bounds the proportion of such `γ_i`,
and Fubini over the product `𝔉_n` gives the factor `k_n`. Part (i): the easy cases here
(`partOne_of_core`), the core in `P8Core.core_one`. Also Lemma 7.17 for the inverses `γ⁻¹` and
`θ⁻¹` (`partOne_inv`, `part2_inv`; not milestones).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace P8G5

open ConstrDisp

theorem piSplitAt_symm_eq_update {ι : Type*} [DecidableEq ι] {β : ι → Type*} (c : ι)
    (a a0 : β c) (r : ∀ j : {j // j ≠ c}, β j) :
    (Equiv.piSplitAt c β).symm (a, r) =
      Function.update ((Equiv.piSplitAt c β).symm (a0, r)) c a := by
  funext j
  by_cases hj : j = c
  · subst hj
    simp [Equiv.piSplitAt]
  · rw [Function.update_of_ne hj]
    simp [Equiv.piSplitAt, hj]

/-- Fubini for a union bound over one coordinate of a finite product. -/
theorem card_filter_le_of_slice {ι : Type*} [DecidableEq ι] [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (c : ι) (P : (∀ i, β i) → Prop) [DecidablePred P] (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ γ : (∀ i, β i),
      ((Finset.univ.filter fun a : β c => P (Function.update γ c a)).card : ℝ) ≤
        B * Fintype.card (β c)) :
    ((Finset.univ.filter P).card : ℝ) ≤ B * Fintype.card (∀ i, β i) := by
  classical
  set e := Equiv.piSplitAt c β
  have hcard : Fintype.card (∀ i, β i) =
      Fintype.card (β c) * Fintype.card (∀ j : {j // j ≠ c}, β j) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have h1 : (Finset.univ.filter P).card = ∑ r : (∀ j : {j // j ≠ c}, β j),
      (Finset.univ.filter fun a : β c => P (e.symm (a, r))).card := by
    rw [Finset.card_filter]
    rw [← Fintype.sum_equiv e.symm (fun p => if P (e.symm p) then 1 else 0)
      (fun γ => if P γ then 1 else 0) (fun _ => rfl)]
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun r _ => (Finset.card_filter _ _).symm
  have h2 : ∀ r : (∀ j : {j // j ≠ c}, β j),
      ((Finset.univ.filter fun a : β c => P (e.symm (a, r))).card : ℝ) ≤
        B * Fintype.card (β c) := by
    intro r
    rcases isEmpty_or_nonempty (β c) with hE | ⟨⟨a0⟩⟩
    · simp [Finset.univ_eq_empty]
    · have := h (e.symm (a0, r))
      have hf : (Finset.univ.filter fun a : β c => P (e.symm (a, r))) =
          (Finset.univ.filter fun a : β c => P (Function.update (e.symm (a0, r)) c a)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [piSplitAt_symm_eq_update c a a0 r]
      rw [hf]
      exact this
  rw [h1, hcard]
  push_cast
  calc (∑ r : (∀ j : {j // j ≠ c}, β j),
        ((Finset.univ.filter fun a : β c => P (e.symm (a, r))).card : ℝ))
      ≤ ∑ _r : (∀ j : {j // j ≠ c}, β j), B * Fintype.card (β c) :=
        Finset.sum_le_sum fun r _ => h2 r
    _ = B * (Fintype.card (β c) * Fintype.card (∀ j : {j // j ≠ c}, β j)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The triangle inequality along the intermediate points of a product, pointwise. -/
theorem dist_prod_pt (ω : ℕ → Fin 3) : ∀ (l : List BinaryTreeAut), (∀ g ∈ l, g ∈ grigorchuk ω) →
    ∀ x ∈ orbitOne ω, ∀ b : ℕ → ℕ, (∀ i (h : i < l.length),
      schreierDist ω (x <• (l.take i).prod) ((x <• (l.take i).prod) <• l[i]) ≤ b i) →
    schreierDist ω x (x <• l.prod) ≤ ∑ i ∈ Finset.range l.length, b i := by
  intro l
  induction l with
  | nil =>
    intro _ x hx b _
    simp only [List.prod_nil]
    rw [show x <• (1 : BinaryTreeAut) = x from one_smul _ x, dist_self ω x (cofinal_of_orbit ω x hx)]
    exact Nat.zero_le _
  | cons g l ih =>
    intro hl x hx b hb
    have hg : g ∈ grigorchuk ω := hl g (by simp)
    have hxg := orbit_smul ω x hx g hg
    have hlp : l.prod ∈ grigorchuk ω :=
      Subgroup.list_prod_mem _ fun s hs => hl s (by simp [hs])
    have hrest := ih (fun s hs => hl s (by simp [hs])) (x <• g) hxg (fun i => b (i + 1))
      (fun i h => by
        have := hb (i + 1) (by simpa using h)
        simpa [List.take_succ_cons, List.prod_cons, MulOpposite.op_mul, mul_smul] using this)
    have h0 := hb 0 (by simp)
    simp only [List.take_zero, List.prod_nil, List.getElem_cons_zero] at h0
    rw [show x <• (1 : BinaryTreeAut) = x from one_smul _ x] at h0
    rw [List.prod_cons, MulOpposite.op_mul, mul_smul, List.length_cons, Finset.sum_range_succ']
    have hxgl := orbit_smul ω _ hxg _ hlp
    refine (dist_triangle ω x (x <• g) _ (cofinal_of_orbit ω x hx)
      (cofinal_of_orbit ω _ hxg) (cofinal_of_orbit ω _ hxgl)).trans ?_
    rw [add_comm (∑ i ∈ Finset.range l.length, b (i + 1))]
    exact Nat.add_le_add h0 hrest

theorem fSet_finite (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) :
    (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · refine ((List.finite_length_eq Bool (D - j % D + 2 * k n + frM D ω (ellIndex D (2 * k n) j)
      + 3)).image (gTilde ω j)).subset ?_
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, ConstrH.length_of_mem_vSet D ω j _ v hv, rfl⟩
  · exact Set.finite_singleton _

/-- The uniform measure of a finite set: a count. -/
theorem card_le_of_mass_le (F : Set BinaryTreeAut) [Fintype ↥F] (A : Set BinaryTreeAut)
    [DecidablePred (· ∈ A)] (B : ℝ) (hB : 0 ≤ B) (h : mass (uniformMeasure F) A ≤ B) :
    ((Finset.univ.filter fun a : ↥F => (a : BinaryTreeAut) ∈ A).card : ℝ) ≤
      B * Fintype.card ↥F := by
  classical
  have hsupp : Function.support (A.indicator (uniformMeasure F)) ⊆ F := by
    intro g hg
    by_contra hgF
    apply hg
    simp [Set.indicator, uniformMeasure, hgF]
  have hm : mass (uniformMeasure F) A =
      ((Finset.univ.filter fun a : ↥F => (a : BinaryTreeAut) ∈ A).card : ℝ) *
        (Nat.card ↥F : ℝ)⁻¹ := by
    unfold mass
    rw [← tsum_subtype_eq_of_support_subset hsupp, tsum_fintype]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (a : BinaryTreeAut) ∈ A
    · simp [Set.indicator, ha, uniformMeasure]
    · simp [Set.indicator, ha]
  rw [Nat.card_eq_fintype_card] at hm
  rcases Nat.eq_zero_or_pos (Fintype.card ↥F) with h0 | hpos
  · have : (Finset.univ.filter fun a : ↥F => (a : BinaryTreeAut) ∈ A).card = 0 := by
      have := Finset.card_le_univ (Finset.univ.filter fun a : ↥F => (a : BinaryTreeAut) ∈ A)
      omega
    rw [this, h0]; simp
  · have hpos' : (0 : ℝ) < Fintype.card ↥F := by exact_mod_cast hpos
    rw [hm] at h
    have := mul_le_mul_of_nonneg_right h hpos'.le
    rwa [mul_assoc, inv_mul_cancel₀ hpos'.ne', mul_one] at this

/-- Membership and the displacement of the levels `{g_j}`. -/
theorem level_facts (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (γ : BinaryTreeAut) (hγ : γ ∈ fSet D ω k j n) :
    γ ∈ grigorchuk ω ∧ (¬(ω (j - 1) = 2 ∧ n < j + k n ∧ j ≤ n) →
      ∀ x ∈ orbitOne ω, schreierDist ω x (x <• γ) ≤ 2 ^ (j + 2)) := by
  obtain ⟨hF1, -, -⟩ := seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω
  unfold fSet at hγ
  split_ifs at hγ with hc
  · obtain ⟨hj, hjn1, hjn'⟩ := hc
    obtain ⟨v, hv, hpre, rfl⟩ := hγ
    have hkn := hk.2 n (by omega) hn
    have h2k : D ∣ 2 * k n := Dvd.dvd.mul_left hkn.2 2
    have hmem := (exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω j hj1
      (2 * k n) h2k v hv).2.1
    exact ⟨hmem, fun h => absurd ⟨hj, hjn1, hjn'⟩ h⟩
  · rw [Set.mem_singleton_iff.mp hγ]
    obtain ⟨hst, hsec⟩ := hF1 j hj1
    refine ⟨hst.1, fun _ x hx => ?_⟩
    have hA := (sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal ω (seqG ω j) hst.1 j x
      (cofinal_of_orbit ω x hx)).2
    refine hA.trans ?_
    have hl : wordLength (gens (shiftSeq ω j)) (sec (seqG ω j) (rayPrefix x j)) ≤ 2 := by
      have ha : grigA ∈ gens (shiftSeq ω j) := by simp [gens]
      have key : ∀ γ : BCD, wordLength (gens (shiftSeq ω j)) (grigA * gen (shiftSeq ω j) γ) ≤ 2 ∧
          wordLength (gens (shiftSeq ω j)) (grigA * (grigA * gen (shiftSeq ω j) γ) * grigA) ≤ 2 := by
        intro γ
        have hγ : gen (shiftSeq ω j) γ ∈ gens (shiftSeq ω j) := by cases γ <;> simp [gens]
        constructor
        · have := wordLength_le_of_list (shiftSeq ω j) [grigA, gen (shiftSeq ω j) γ]
            (by simp [ha, hγ])
          simpa using this
        · have := wordLength_le_of_list (shiftSeq ω j) [gen (shiftSeq ω j) γ, grigA]
            (by simp [ha, hγ])
          rw [← mul_assoc grigA grigA, show grigA * grigA = 1 from
            Subtype.ext (Equiv.ext fun w => grigAFun_involutive w), one_mul]
          simpa using this
      rcases hsec (rayPrefix x j) (length_rayPrefix _ _) with h | h <;> rw [h] <;> split_ifs <;>
        simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one] <;>
        first | exact (key .c).1 | exact (key .c).2 | exact (key .b).1 | exact (key .b).2
    calc 2 ^ j * (wordLength (gens (shiftSeq ω j)) (sec (seqG ω j) (rayPrefix x j)) + 1)
        ≤ 2 ^ j * 2 ^ 2 := by gcongr; norm_num; omega
      _ = 2 ^ (j + 2) := (pow_add 2 j 2).symm

theorem geom_sum (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ (n - i + 2) + 8 = 2 ^ (n + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range n, 2 ^ (n + 1 - (i + 1) + 2) = 2 ^ (n - i + 2) := by
      intro i _; congr 2; omega
    rw [Finset.sum_congr rfl this]
    have h2 : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by ring
    rw [show n + 1 - 0 + 2 = n + 3 by omega, h2]
    omega

/-- Part (i) of the stub of Lemma 7.17, as a predicate. -/
def PartOne (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → n ≤ j + k n → j ≤ n → ω (j - 1) = 2 →
    ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
      mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
        (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2)

/-- Lemma 7.17 (ii) from Lemma 7.17 (i): the union bound of p. 45. -/
theorem part2_of_part1 (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) (h1 : PartOne D ω k n) :
    ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
      (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
          ℝ) / Nat.card (fProd D ω k n) ≤
        8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
  classical
  intro ε ℓ hℓ1 _hℓ2 x hx
  have hD : 3 ≤ D := (ConstrW.frM_spec D ω hω 0).1.trans' (by omega)
  have hkn : 1 ≤ k n := (hk.2 n hn1 hn).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  letI : ∀ i : Fin n, Fintype ↥(fSet D ω k (i + 1) n) :=
    fun i => (fSet_finite D ω k (i + 1) n).fintype
  set M := Fintype.card (fProd D ω k n) with hM
  have hMc : Nat.card (fProd D ω k n) = M := Nat.card_eq_fintype_card
  set Q : fProd D ω k n → Prop :=
    fun γ => k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ)) with hQ
  have hNc : Nat.card {γ : fProd D ω k n // Q γ} = (Finset.univ.filter Q).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hMc, hNc]
  have hRHS0 : 0 ≤ 8 * (k n : ℝ) * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by positivity
  have hNM : (Finset.univ.filter Q).card ≤ M := Finset.card_le_univ _
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0, Nat.cast_zero, div_zero]; exact hRHS0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  rw [div_le_iff₀ hMr]
  by_cases hsmall : ℓ ≤ n + 3 * D
  · have h8 : (1 : ℝ) ≤ 8 * (k n : ℝ) * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
      have he : (-3 : ℝ) ≤ -(((ℓ : ℝ) - n) / D) := by
        rw [neg_le_neg_iff, div_le_iff₀ hDr]
        have : (ℓ : ℝ) ≤ n + 3 * D := by exact_mod_cast hsmall
        linarith
      have hp : (2 : ℝ) ^ (-3 : ℝ) ≤ (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      have h3 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
        rw [Real.rpow_neg (by norm_num)]; norm_num
      have hk1 : (1 : ℝ) ≤ k n := by exact_mod_cast hkn
      rw [h3] at hp
      nlinarith
    have : ((Finset.univ.filter Q).card : ℝ) ≤ M := by exact_mod_cast hNM
    nlinarith
  push_neg at hsmall
  -- the list of factors, the intermediate points, the bad events
  set thL : fProd D ω k n → List BinaryTreeAut := fun γ =>
    List.ofFn fun i : Fin n => ((γ i.rev : BinaryTreeAut)) ^ (ε i.rev).toNat with hthL
  have htheta : ∀ γ, theta D ω k n (ε, γ) = (thL γ).prod := fun γ => rfl
  set z : Fin n → fProd D ω k n → Ray :=
    fun c γ => x <• ((thL γ).take (n - 1 - c)).prod with hz
  set gtl : Fin n → Prop := fun c => ω c = 2 ∧ n < c + 1 + k n with hgtl
  set P : Fin n → fProd D ω k n → Prop := fun c γ => gtl c ∧ ε c = true ∧
      2 ^ (ℓ - 1) ≤ schreierDist ω (z c γ) (z c γ <• (γ c : BinaryTreeAut)) with hP
  have hmemF : ∀ (γ : fProd D ω k n) (c : Fin n), (γ c : BinaryTreeAut) ∈ grigorchuk ω :=
    fun γ c => (level_facts D ω hω k hk n hn (c + 1) (by omega) (by omega) _ (γ c).2).1
  have hmemL : ∀ γ, ∀ g ∈ thL γ, g ∈ grigorchuk ω := by
    intro γ g hg
    rw [hthL, List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact Subgroup.pow_mem _ (hmemF γ i.rev) _
  have hzorb : ∀ c γ, z c γ ∈ orbitOne ω := by
    intro c γ
    exact orbit_smul ω x hx _ (Subgroup.list_prod_mem _ fun g hg =>
      hmemL γ g (List.mem_of_mem_take hg))
  have hzind : ∀ (c : Fin n) (γ : fProd D ω k n) (a : ↥(fSet D ω k (c + 1) n)),
      z c (Function.update γ c a) = z c γ := by
    intro c γ a
    simp only [hz]
    congr 3
    apply List.ext_getElem
    · simp [hthL]
    · intro i h1 h2
      simp only [hthL, List.getElem_take, List.getElem_ofFn]
      have hne : Fin.rev ⟨i, by simp [hthL] at h1; omega⟩ ≠ c := by
        intro h
        have := congrArg Fin.val h
        simp [Fin.rev] at this h1
        omega
      rw [Function.update_of_ne hne]
  -- Step A: a large displacement has a bad level
  have stepA : ∀ γ, Q γ → ∃ c, P c γ := by
    intro γ hQγ
    by_contra hno
    push_neg at hno
    set b : ℕ → ℕ := fun i => 2 ^ (n - i + 2) +
      if (ω (n - 1 - i) = 2 ∧ n < n - i + k n) then 2 ^ (ℓ - 1) else 0 with hb
    have hlen : (thL γ).length = n := by simp [hthL]
    have hd := dist_prod_pt ω (thL γ) (hmemL γ) x hx b (by
      intro i hi
      rw [hlen] at hi
      set c : Fin n := Fin.rev ⟨i, hi⟩ with hc
      have hcv : (c : ℕ) = n - 1 - i := by simp [hc, Fin.rev]; omega
      have hget : (thL γ)[i] = (γ c : BinaryTreeAut) ^ (ε c).toNat := by
        simp only [hthL, List.getElem_ofFn]; rfl
      have htake : (thL γ).take i = (thL γ).take (n - 1 - c) := by
        rw [hcv, show n - 1 - (n - 1 - i) = i by omega]
      rw [hget, htake]
      have hzc : x <• ((thL γ).take (n - 1 - c)).prod = z c γ := rfl
      rw [hzc]
      cases hεc : ε c
      · simp only [Bool.toNat_false, pow_zero]
        rw [show z c γ <• (1 : BinaryTreeAut) = z c γ from one_smul _ _,
          dist_self ω _ (cofinal_of_orbit ω _ (hzorb c γ))]
        exact Nat.zero_le _
      · simp only [Bool.toNat_true, pow_one]
        by_cases hg : gtl c
        · have hlt : schreierDist ω (z c γ) (z c γ <• (γ c : BinaryTreeAut)) < 2 ^ (ℓ - 1) := by
            by_contra hge
            push_neg at hge
            exact hno c ⟨hg, hεc, hge⟩
          have hif : (ω (n - 1 - i) = 2 ∧ n < n - i + k n) := by
            obtain ⟨hg1, hg2⟩ := hg
            refine ⟨?_, by omega⟩
            rw [← hcv]; exact hg1
          simp only [hb, if_pos hif]
          exact hlt.le.trans (Nat.le_add_left _ _)
        · have hnot : ¬(ω (c + 1 - 1) = 2 ∧ n < c + 1 + k n ∧ c + 1 ≤ n) := by
            rintro ⟨h1', h2', -⟩
            exact hg ⟨by simpa using h1', h2'⟩
          have := (level_facts D ω hω k hk n hn (c + 1) (by omega) (by omega) _ (γ c).2).2 hnot
            (z c γ) (hzorb c γ)
          refine this.trans ?_
          simp only [hb]
          refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (Nat.le_add_right _ _)
          omega)
    rw [hlen] at hd
    have hsum : ∑ i ∈ Finset.range n, b i + 8 ≤ 2 ^ (n + 3) + k n * 2 ^ (ℓ - 1) := by
      simp only [hb, Finset.sum_add_distrib]
      have hg := geom_sum n
      have hite : ∑ i ∈ Finset.range n,
          (if (ω (n - 1 - i) = 2 ∧ n < n - i + k n) then 2 ^ (ℓ - 1) else 0) ≤ k n * 2 ^ (ℓ - 1) := by
        calc ∑ i ∈ Finset.range n,
              (if (ω (n - 1 - i) = 2 ∧ n < n - i + k n) then 2 ^ (ℓ - 1) else 0)
            ≤ ∑ i ∈ Finset.range (k n), 2 ^ (ℓ - 1) := by
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset (fun i hi => ?_)
              simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
              omega
          _ = k n * 2 ^ (ℓ - 1) := by simp
      omega
    have hpow : 2 ^ (n + 3) ≤ 2 ^ (ℓ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hℓ : 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hkP : 2 ^ (ℓ - 1) ≤ k n * 2 ^ (ℓ - 1) := Nat.le_mul_of_pos_left _ hkn
    have hQ' : k n * 2 ^ ℓ ≤ schreierDist ω x (x <• (thL γ).prod) := by
      rw [← htheta]; exact hQγ
    rw [hℓ, show k n * (2 * 2 ^ (ℓ - 1)) = 2 * (k n * 2 ^ (ℓ - 1)) by ring] at hQ'
    omega
  -- Step B: each bad event, by Fubini and (i)
  set B : ℝ := (2 : ℝ) ^ (-((((ℓ - 1 : ℕ) : ℝ) - n) / D) + 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have stepB : ∀ c : Fin n, ((Finset.univ.filter (P c)).card : ℝ) ≤
      (if gtl c then B else 0) * M := by
    intro c
    by_cases hg : gtl c
    · rw [if_pos hg, hM]
      refine card_filter_le_of_slice c (P c) B hB0 (fun γ => ?_)
      by_cases hεc : ε c = true
      · set A : Set BinaryTreeAut :=
          {g | 2 ^ (ℓ - 1) ≤ schreierDist ω (z c γ) (z c γ <• g)} with hA
        have hfeq : (Finset.univ.filter fun a : ↥(fSet D ω k (c + 1) n) =>
            P c (Function.update γ c a)) =
            Finset.univ.filter fun a : ↥(fSet D ω k (c + 1) n) => (a : BinaryTreeAut) ∈ A := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP, hA, Set.mem_setOf_eq,
            hzind c γ a, Function.update_self]
          exact ⟨fun h => h.2.2, fun h => ⟨hg, hεc, h⟩⟩
        rw [hfeq]
        by_cases hℓc : ℓ - 1 ≤ (c + 1) + 2 * k n + 2 * D + 4
        · have hm := h1 (c + 1) (by omega) (by have := hg.2; omega) (by omega)
            (by simpa using hg.1) (ℓ - 1) (by omega) hℓc (z c γ) (hzorb c γ)
          exact card_le_of_mass_le _ A B hB0 hm
        · have hempty : (Finset.univ.filter fun a : ↥(fSet D ω k (c + 1) n) =>
              (a : BinaryTreeAut) ∈ A) = ∅ := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA, Set.mem_setOf_eq,
              Finset.notMem_empty, iff_false, not_le]
            have := (schreierDist_smul_le_of_mem_fSet_and_smul_theta_le D ω hω k hk n hn).1
              (c + 1) (by omega) (by omega) a a.2 (z c γ) (hzorb c γ)
            refine lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) (by omega))
          rw [hempty, Finset.card_empty, Nat.cast_zero]
          positivity
      · have hempty : (Finset.univ.filter fun a : ↥(fSet D ω k (c + 1) n) =>
            P c (Function.update γ c a)) = ∅ := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP,
            Finset.notMem_empty, iff_false]
          exact fun h => hεc h.2.1
        rw [hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    · rw [if_neg hg, zero_mul]
      have hempty : Finset.univ.filter (P c) = ∅ := by
        ext γ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP, Finset.notMem_empty,
          iff_false]
        exact fun h => hg h.1
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  -- Step C: at most `k_n` levels are made of `g̃`'s
  have hcount : ((Finset.univ.filter gtl).card : ℝ) ≤ k n := by
    have : (Finset.univ.filter gtl).card ≤ k n := by
      calc (Finset.univ.filter gtl).card
          = ((Finset.univ.filter gtl).map Fin.valEmbedding).card := (Finset.card_map _).symm
        _ ≤ (Finset.Ico (n - k n) n).card := by
            refine Finset.card_le_card (fun i hi => ?_)
            simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
              Fin.valEmbedding_apply, hgtl] at hi
            obtain ⟨c, ⟨-, hc2⟩, rfl⟩ := hi
            simp only [Finset.mem_Ico]
            omega
        _ ≤ k n := by simp only [Nat.card_Ico]; omega
    exact_mod_cast this
  have hunion : (Finset.univ.filter Q) ⊆ Finset.univ.biUnion (fun c => Finset.univ.filter (P c)) := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨c, hc⟩ := stepA γ hγ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨c, hc⟩
  have hN : ((Finset.univ.filter Q).card : ℝ) ≤ k n * B * M := by
    calc ((Finset.univ.filter Q).card : ℝ)
        ≤ ((Finset.univ.biUnion (fun c => Finset.univ.filter (P c))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hunion
      _ ≤ ∑ c : Fin n, ((Finset.univ.filter (P c)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ c : Fin n, (if gtl c then B else 0) * M := Finset.sum_le_sum fun c _ => stepB c
      _ = ((Finset.univ.filter gtl).card : ℝ) * B * M := by
          rw [← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ k n * B * M := by gcongr
  -- the constant
  have hBle : B ≤ 8 * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
    have hcast : (((ℓ - 1 : ℕ) : ℝ)) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h8 : (8 : ℝ) * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) =
        (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 3) := by
      rw [Real.rpow_add (by norm_num)]
      norm_num
      ring
    rw [h8, hBdef, hcast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hD1 : (1 : ℝ) / D ≤ 1 := by
      rw [div_le_one hDr]; exact_mod_cast (show 1 ≤ D by omega)
    have : ((ℓ : ℝ) - 1 - n) / D = ((ℓ : ℝ) - n) / D - 1 / D := by
      field_simp; ring
    rw [this]
    linarith
  have hk0 : (0 : ℝ) ≤ k n := by positivity
  calc ((Finset.univ.filter Q).card : ℝ) ≤ k n * B * M := hN
    _ ≤ k n * (8 * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D))) * M := by gcongr
    _ = 8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) * M := by ring

/-- The uniform measure of a finite set gives every set mass at most `1`. -/
theorem mass_uniformMeasure_le_one (F : Set BinaryTreeAut) (hF : F.Finite) (A : Set BinaryTreeAut) :
    mass (uniformMeasure F) A ≤ 1 := by
  classical
  letI : Fintype ↥F := hF.fintype
  have hsupp : Function.support (A.indicator (uniformMeasure F)) ⊆ F := by
    intro g hg
    by_contra hgF
    apply hg
    simp [Set.indicator, uniformMeasure, hgF]
  unfold mass
  rw [← tsum_subtype_eq_of_support_subset hsupp, tsum_fintype]
  calc ∑ a : ↥F, A.indicator (uniformMeasure F) (a : BinaryTreeAut)
      ≤ ∑ _a : ↥F, (Nat.card ↥F : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : (a : BinaryTreeAut) ∈ A
        · simp [Set.indicator, ha, uniformMeasure]
        · simp only [Set.indicator, ha, if_false]; positivity
    _ ≤ 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        rcases Nat.eq_zero_or_pos (Fintype.card ↥F) with h0 | hpos
        · rw [h0]; simp
        · rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne')]

/-- The part of Lemma 7.17 (i) that is not settled here: the levels made of `g̃`'s
(`n - k_n < j`), and `ℓ > n + 2D` (for `ℓ ⩽ n + 2D` the bound is `⩾ 1`). -/
def CoreOne (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → n < j + k n → j ≤ n → ω (j - 1) = 2 →
    ∀ ℓ : ℕ, n + 2 * D < ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
      mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
        (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2)

/-- Lemma 7.17 (i) from its core: the range `ℓ ⩽ n + 2D` and the level `j = n - k_n`
(where `𝔉_{j,n} = {g_j}` moves every point by at most `2^{j+2} < 2^ℓ`). -/
theorem partOne_of_core (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) (hcore : CoreOne D ω k n) :
    PartOne D ω k n := by
  classical
  intro j hj1 hjk hjn hωj ℓ hℓ1 hℓ2 x hx
  have hD : 3 ≤ D := (ConstrW.frM_spec D ω hω 0).1.trans' (by omega)
  have hDr : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hkn : 1 ≤ k n := (hk.2 n hn1 hn).1
  by_cases hsmall : ℓ ≤ n + 2 * D
  · refine (mass_uniformMeasure_le_one _ (fSet_finite D ω k j n) _).trans ?_
    apply Real.one_le_rpow (by norm_num)
    have : ((ℓ : ℝ) - n) / D ≤ 2 := by
      rw [div_le_iff₀ hDr]
      have : (ℓ : ℝ) ≤ n + 2 * D := by exact_mod_cast hsmall
      linarith
    linarith
  push_neg at hsmall
  by_cases hc : n < j + k n
  · exact hcore j hj1 hc hjn hωj ℓ hsmall hℓ2 x hx
  · have hF : fSet D ω k j n = {seqG ω j} := by
      unfold fSet
      rw [if_neg (fun h => hc h.2.1)]
    have hd := (level_facts D ω hω k hk n hn j hj1 hjn (seqG ω j) (by rw [hF]; rfl)).2
      (fun h => hc h.2.1) x hx
    have hzero : mass (uniformMeasure (fSet D ω k j n))
        {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} = 0 := by
      unfold mass
      have : ∀ g, Set.indicator {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)}
          (uniformMeasure (fSet D ω k j n)) g = 0 := by
        intro g
        by_cases hg : g = seqG ω j
        · subst hg
          have hlt : schreierDist ω x (x <• seqG ω j) < 2 ^ ℓ :=
            lt_of_le_of_lt hd (Nat.pow_lt_pow_right (by norm_num) (by omega))
          simp [Set.indicator, not_le.mpr hlt]
        · have : g ∉ fSet D ω k j n := by rw [hF]; exact hg
          simp [Set.indicator, uniformMeasure, this]
      simp [this]
    rw [hzero]
    positivity

/-- **Lemma 7.17 from its core.** The stub of Lemma 7.17 (both parts), given `CoreOne`. -/
theorem mass_uniformMeasure_fSet_le_and_card_fProd_le_of_core (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) (hcore : CoreOne D ω k n) :
    (∀ j, 1 ≤ j → n ≤ j + k n → j ≤ n → ω (j - 1) = 2 →
      ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
        mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
          (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2)) ∧
    ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
      (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
          ℝ) / Nat.card (fProd D ω k n) ≤
        8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) := by
  have h1 := partOne_of_core D ω hω k hk n hn hn1 hcore
  exact ⟨h1, part2_of_part1 D ω hω k hk n hn hn1 h1⟩


end P8G5


end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (hn1 : 1 ≤ n) :
    (∀ j, 1 ≤ j → n ≤ j + k n → j ≤ n → ω (j - 1) = 2 →
      ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ j + 2 * k n + 2 * D + 4 → ∀ x ∈ orbitOne ω,
        mass (uniformMeasure (fSet D ω k j n)) {γ | 2 ^ ℓ ≤ schreierDist ω x (x <• γ)} ≤
          (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D) + 2)) ∧
    ∀ ε : Fin n → Bool, ∀ ℓ : ℕ, n ≤ ℓ → ℓ ≤ n + 2 * k n + 2 * D + 5 → ∀ x ∈ orbitOne ω,
      (Nat.card {γ : fProd D ω k n // k n * 2 ^ ℓ ≤ schreierDist ω x (x <• theta D ω k n (ε, γ))} :
          ℝ) / Nat.card (fProd D ω k n) ≤
        8 * k n * (2 : ℝ) ^ (-(((ℓ : ℝ) - n) / D)) :=
  P8G5.mass_uniformMeasure_fSet_le_and_card_fProd_le_of_core D ω hω k hk n hn hn1
    (P8Core.core_one D ω hω k hk n hn hn1)
end
