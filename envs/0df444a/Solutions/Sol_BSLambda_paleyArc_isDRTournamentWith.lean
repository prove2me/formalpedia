-- Prove2me | solution 1 for BSLambda.paleyArc_isDRTournamentWith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:10:20.683882+00:00
-- url     : https://prove2.me/submissions/56dc794b-711f-43f3-92f3-c8850c28c9de

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Theorems.Thm_two_mul_card_quadraticChar_eq_one
public import Theorems.Thm_quadraticChar_sub_swap
public import Theorems.Thm_four_mul_card_quadraticChar_sub_eq_one
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs


section
@[expose] public section
open Finset
section QuadraticCharSums
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end QuadraticCharSums
namespace BSLambda
section Paley
private theorem card_filter_quadraticChar_sub_eq_one {k t : ℕ} [Fact (Nat.Prime k)]
    (hchar : ringChar (ZMod k) ≠ 2) (hneg : quadraticChar (ZMod k) (-1) = -1)
    (ht : 4 * t + 3 = k) {a b : ZMod k} (hab : a ≠ b) :
    (univ.filter fun z : ZMod k ↦
        quadraticChar (ZMod k) (z - a) = 1 ∧ quadraticChar (ZMod k) (z - b) = 1).card = t := by
  have h := four_mul_card_quadraticChar_sub_eq_one hchar hneg hab
  rw [ZMod.card] at h
  omega
end Paley
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda
namespace BSLambda
theorem _root_.solution {k d t : ℕ} [Fact (Nat.Prime k)]
    (hchar : ringChar (ZMod k) ≠ 2) (hneg : quadraticChar (ZMod k) (-1) = -1)
    (hd : 2 * d + 1 = k) (ht : 4 * t + 3 = k) : IsDRTournamentWith (paleyArc k) d t where
  arc_self i := by
    simp only [paleyArc, sub_self, quadraticChar_zero, decide_eq_false_iff_not]
    decide
  arc_eq_not_arc := fun {i j} hij ↦ by
    have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp only [paleyArc, quadraticChar_sub_swap hneg i j]
    rcases quadraticChar_dichotomy hji with h | h <;> rw [h] <;> decide
  card_outNbrs i := by
    have hcard : (outNbrs (paleyArc k) i).card
        = (univ.filter fun a : ZMod k ↦ quadraticChar (ZMod k) a = 1).card :=
      Finset.card_equiv (Equiv.subRight i) (by simp [paleyArc])
    have h := two_mul_card_quadraticChar_eq_one (F := ZMod k) hchar
    rw [ZMod.card] at h
    omega
  card_commonOut := fun {i j} hij ↦ by
    have hset : commonOut (paleyArc k) i j = univ.filter fun z : ZMod k ↦
        quadraticChar (ZMod k) (z - i) = 1 ∧ quadraticChar (ZMod k) (z - j) = 1 := by
      ext x
      simp [paleyArc]
    rw [hset]
    exact card_filter_quadraticChar_sub_eq_one hchar hneg ht hij
  card_commonIn := fun {i j} hij ↦ by
    have hcard : (commonIn (paleyArc k) i j).card
        = (univ.filter fun z : ZMod k ↦ quadraticChar (ZMod k) (z - -i) = 1
            ∧ quadraticChar (ZMod k) (z - -j) = 1).card := by
      refine Finset.card_equiv (Equiv.neg (ZMod k)) fun x ↦ ?_
      simp only [paleyArc, decide_eq_true_eq, mem_commonIn, mem_filter, mem_univ, true_and,
        Equiv.neg_apply, show ∀ u : ZMod k, -x - -u = u - x from fun u ↦ by ring]
    rw [hcard]
    exact card_filter_quadraticChar_sub_eq_one hchar hneg ht fun h ↦ hij (neg_injective h)
end BSLambda
