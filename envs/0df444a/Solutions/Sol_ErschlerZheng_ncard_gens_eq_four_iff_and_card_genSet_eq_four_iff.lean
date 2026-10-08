-- Prove2me | solution 1 for ErschlerZheng.ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T12:44:17.436981+00:00
-- url     : https://prove2.me/submissions/aff906f8-3a38-465d-9169-f70730da40f5

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction

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

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

/-- Whether `g` swaps the two vertices of level 1. -/
def rootSwap (g : BinaryTreeAut) : Bool := decide ([false] <• g = [true])

theorem rootSwap_one : rootSwap 1 = false := by
  unfold rootSwap; simp

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

end GrigBasic

end ErschlerZheng
end

section
/-!
# Fr(D), the four generators, and the index arithmetic of §7.2 (group `frarith`)

Proofs of five small statements backing sentences of the notes:

* `chk_exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr`:
  under `SatisfiesFr D ω` the letters `1` and `2` occur after every position, so the tail
  hypotheses of the `evalFree` and `letterGerms` milestones hold and `ω` is not constant;
* `chk_ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff`: `a, b_ω, c_ω, d_ω` are four distinct
  elements exactly when `ω` is not constant;
* `chk_isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq`: `k_n = A⌊log₂ n⌋` is admissible;
* `chk_mul_ellIndex_eq_iff_dvd`: the ℕ division in `ellIndex` is exact iff `D ∣ k`;
* `chk_dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq`: the
  exponent of `|𝔉_{j,n}|` is computed exactly in ℕ.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace NewFrArith

open GrigBasic

/-! ### Item 1: letters `1` and `2` in every tail -/

/-! ### Item 2: the four generators -/

theorem grigA_ne_gen (ω : ℕ → Fin 3) (γ : BCD) : grigA ≠ gen ω γ := by
  intro h
  have := rootSwap_grigA
  rw [h, rootSwap_gen] at this
  exact Bool.false_ne_true this

theorem grigA_ne_one : grigA ≠ 1 := by
  intro h
  have := rootSwap_grigA
  rw [h, rootSwap_one] at this
  exact Bool.false_ne_true this

theorem sec_gen_replicate (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-- Two generators differ as soon as some letter of `ω` takes different values at them. -/
theorem gen_ne_of_letterValue_ne (ω : ℕ → Fin 3) (γ γ' : BCD) (n : ℕ)
    (h : letterValue (ω n) γ ≠ letterValue (ω n) γ') : gen ω γ ≠ gen ω γ' := by
  intro he
  have hs := congrArg (fun g => sec g (List.replicate n true ++ [false])) he
  simp only [sec_append, sec_gen_replicate, sec_gen_false] at hs
  unfold letterElt at hs
  simp only [shiftSeq, zero_add] at hs
  cases h1 : letterValue (ω n) γ <;> cases h2 : letterValue (ω n) γ' <;>
    simp only [h1, h2, ne_eq, not_true_eq_false] at h hs
  · simp at hs
    exact grigA_ne_one hs.symm
  · simp at hs
    exact grigA_ne_one hs

theorem genFun_eq_of_letterValue_eq (γ γ' : BCD) :
    ∀ (w : List Bool) (ω : ℕ → Fin 3), (∀ n, letterValue (ω n) γ = letterValue (ω n) γ') →
      genFun ω γ w = genFun ω γ' w := by
  intro w
  induction w with
  | nil => intro ω _; rfl
  | cons x w ih =>
    intro ω h
    cases x
    · simp only [genFun, h 0]
    · simp only [genFun]
      rw [ih (shiftSeq ω 1) (fun n => h (n + 1))]

theorem gen_eq_of_letterValue_eq (ω : ℕ → Fin 3) (γ γ' : BCD)
    (h : ∀ n, letterValue (ω n) γ = letterValue (ω n) γ') : gen ω γ = gen ω γ' :=
  Subtype.ext (Equiv.ext fun w => genFun_eq_of_letterValue_eq γ γ' w ω h)

theorem ncard_le_three_of_subset {α : Type*} {s : Set α} {x y z : α} (h : s ⊆ {x, y, z}) :
    s.ncard ≤ 3 := by
  refine (Set.ncard_le_ncard h (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  have := Set.ncard_insert_le y {z}
  rw [Set.ncard_singleton] at this
  omega

theorem gens_distinct_of_exists_ne (ω : ℕ → Fin 3) (hω : ∃ m n, ω m ≠ ω n) :
    grigA ≠ gen ω .b ∧ grigA ≠ gen ω .c ∧ grigA ≠ gen ω .d ∧ gen ω .b ≠ gen ω .c ∧
      gen ω .b ≠ gen ω .d ∧ gen ω .c ≠ gen ω .d := by
  obtain ⟨m, n, hmn⟩ := hω
  -- some letter differs from each of `0`, `1`, `2`
  have hex : ∀ i : Fin 3, ∃ p, ω p ≠ i := by
    intro i
    by_cases hm : ω m = i
    · exact ⟨n, fun hn => hmn (hm.trans hn.symm)⟩
    · exact ⟨m, hm⟩
  obtain ⟨p0, hp0⟩ := hex 0
  obtain ⟨p1, hp1⟩ := hex 1
  obtain ⟨p2, hp2⟩ := hex 2
  have hcases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i; fin_cases i <;> simp
  refine ⟨grigA_ne_gen ω _, grigA_ne_gen ω _, grigA_ne_gen ω _, ?_, ?_, ?_⟩
  · -- `b ≠ c`: some letter is `1` or `2`
    apply gen_ne_of_letterValue_ne ω _ _ p0
    rcases hcases (ω p0) with h | h | h
    · exact absurd h hp0
    all_goals simp [h, letterValue, BCD.killedBy]
  · -- `b ≠ d`: some letter is `0` or `2`
    apply gen_ne_of_letterValue_ne ω _ _ p1
    rcases hcases (ω p1) with h | h | h
    · simp [h, letterValue, BCD.killedBy]
    · exact absurd h hp1
    · simp [h, letterValue, BCD.killedBy]
  · -- `c ≠ d`: some letter is `0` or `1`
    apply gen_ne_of_letterValue_ne ω _ _ p2
    rcases hcases (ω p2) with h | h | h
    · simp [h, letterValue, BCD.killedBy]
    · simp [h, letterValue, BCD.killedBy]
    · exact absurd h hp2

theorem ncard_gens_le_three_of_const (ω : ℕ → Fin 3) (hω : ¬ ∃ m n, ω m ≠ ω n) :
    (gens ω).ncard ≤ 3 := by
  push Not at hω
  have hcases : ω 0 = 0 ∨ ω 0 = 1 ∨ ω 0 = 2 := by
    rcases ω 0 with ⟨k, hk⟩
    interval_cases k <;> simp
  unfold gens
  rcases hcases with h | h | h
  · -- constant `0`: `b = c`
    have hbc : gen ω .b = gen ω .c :=
      gen_eq_of_letterValue_eq ω _ _ fun n => by
        rw [hω n 0, h]; simp [letterValue, BCD.killedBy]
    apply ncard_le_three_of_subset (x := grigA) (y := gen ω .b) (z := gen ω .d)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inl (hx.trans hbc.symm))
    · exact Or.inr (Or.inr hx)
  · -- constant `1`: `b = d`
    have hbd : gen ω .b = gen ω .d :=
      gen_eq_of_letterValue_eq ω _ _ fun n => by
        rw [hω n 0, h]; simp [letterValue, BCD.killedBy]
    apply ncard_le_three_of_subset (x := grigA) (y := gen ω .b) (z := gen ω .c)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inl (hx.trans hbd.symm))
  · -- constant `2`: `c = d`
    have hcd : gen ω .c = gen ω .d :=
      gen_eq_of_letterValue_eq ω _ _ fun n => by
        rw [hω n 0, h]; simp [letterValue, BCD.killedBy]
    apply ncard_le_three_of_subset (x := grigA) (y := gen ω .b) (z := gen ω .c)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inr (hx.trans hcd.symm))

theorem ncard_gens_eq_four_iff (ω : ℕ → Fin 3) : (gens ω).ncard = 4 ↔ ∃ m n, ω m ≠ ω n := by
  constructor
  · intro h
    by_contra hc
    have := ncard_gens_le_three_of_const ω hc
    omega
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gens_distinct_of_exists_ne ω h
    exact Set.ncard_eq_four.2 ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, rfl⟩

theorem card_genSet_eq_ncard_gens (ω : ℕ → Fin 3) : Nat.card (genSet ω) = (gens ω).ncard := by
  rw [Nat.card_coe_set_eq, genSet]
  apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
  intro x hx
  exact ⟨⟨x, Subgroup.subset_closure hx⟩, rfl⟩

/-! ### Item 5: the exponent of `|𝔉_{j,n}|` -/

end NewFrArith

open NewFrArith

end ErschlerZheng
end

section
open scoped RightActions
open Garrido
open ErschlerZheng
open NewFrArith
theorem solution (ω : ℕ → Fin 3) :
    ((gens ω).ncard = 4 ↔ ∃ m n, ω m ≠ ω n) ∧ (Nat.card (genSet ω) = 4 ↔ ∃ m n, ω m ≠ ω n) := by
  rw [card_genSet_eq_ncard_gens]
  exact ⟨ncard_gens_eq_four_iff ω, ncard_gens_eq_four_iff ω⟩
end
