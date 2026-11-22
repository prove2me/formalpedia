-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.tight_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:38.536271+00:00
-- url     : https://prove2.me/submissions/0a8b27ce-3835-4d45-9c78-2b3c51563461

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_far_tight
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (hM : 0 < statePeriodModulus N ρ.length)
    {P Q : {P // P ∈ piecesOf W ρ}} (ht : (shiftSystem W ρ N).IsTight z P Q) :
    FollowerEdge P.val Q.val ∧
      (Q.val.len : ℤ) + statePeriodModulus N ρ.length * z Q <
        (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P + comparisonGap N ρ.length +
            statePeriodModulus N ρ.length := by
  obtain ⟨c, hc, he⟩ := ht
  simp only [shiftSystem] at hc
  split_ifs at hc with hg hn hfar
  · simp only [Option.some.injEq] at hc
    subst c
    have heq : z P = z Q := by omega
    refine ⟨hg, ?_⟩
    rw [heq]
    have hlen : (Q.val.len : ℤ) < (P.val.len : ℤ) +
        comparisonGap N ρ.length := by exact_mod_cast hn.2
    omega
  · simp only [Option.some.injEq] at hc
    subst c
    exact ⟨hg, far_tight hM hfar (by simpa only [sub_eq_add_neg] using he)⟩
end DeciSigma1.Holes.Periodic
