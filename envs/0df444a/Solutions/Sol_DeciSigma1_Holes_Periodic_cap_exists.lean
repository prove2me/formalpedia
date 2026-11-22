-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.cap_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:42.847056+00:00
-- url     : https://prove2.me/submissions/a0317a9d-af8e-4ba7-bbc3-0f874c28a1db

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_least_shifts
public import Theorems.Thm_DeciSigma1_Holes_Periodic_floor_remainder_lt
public import Theorems.Thm_DeciSigma1_Holes_Periodic_retained_cast
public import Theorems.Thm_DeciSigma1_Holes_Periodic_admissible_deletionCounts
public import Theorems.Thm_DeciSigma1_Holes_Periodic_tight_step
public import Theorems.Thm_DeciSigma1_Holes_Periodic_occurrence_path_bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_path_length_bound
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_statePeriodModulus
public import Theorems.Thm_DeciSigma1_Words_IsPrimitive_ne_nil
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
theorem _root_.solution (N : ℕ) {h t : ℕ} (hρ : IsPrimitive ρ)
    (split : OccurrenceSplit W ρ h t) :
    ∃ x, AdmissibleDeletion W ρ N x ∧
      ∀ P ∈ piecesOf W ρ, P.len - statePeriodModulus N ρ.length * x P ≤
          pieceLengthBound N ρ.length h t := by
  have hd : 0 < ρ.length := List.length_pos_iff.mpr hρ.ne_nil
  have hM : 0 < statePeriodModulus N ρ.length := lt_of_lt_of_le hd (d_le_statePeriodModulus _ _)
  obtain ⟨z, hs, hf, _, hz0, hpath⟩ := least_shifts (W := W) (ρ := ρ) N
  refine ⟨deletionCounts z, admissible_deletionCounts hs hf hz0 hM, ?_⟩
  intro P hP
  obtain ⟨p, hnd, hlast, ⟨Q, hhead, hanchor⟩, ht⟩ := hpath ⟨P, hP⟩
  have hg : p.IsChain (fun P Q => FollowerEdge P.val Q.val) :=
    ht.imp (fun _ _ h => (tight_step hM h).1)
  have hplen := occurrence_path_bound split p hnd hg
  cases p with
  | nil => simp at hlast
  | cons R p =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst R
    let v : {P // P ∈ piecesOf W ρ} → ℤ :=
        fun P => (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P
    have hsteps : ∀ A B, (shiftSystem W ρ N).IsTight z A B →
        v B ≤ v A + (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ) := by
      intro A B h
      have := (tight_step hM h).2
      dsimp [v]
      omega
    have hb := path_length_bound v (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ)
      ((shiftSystem W ρ N).IsTight z) hsteps Q p ht
    have hlast' : (Q :: p).getLast (List.cons_ne_nil _ _) = ⟨P, hP⟩ := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
      exact Option.some.inj hlast
    rw [hlast'] at hb
    have hfloor : v Q < (fixedMargin N ρ.length : ℤ) + statePeriodModulus N ρ.length := by
      dsimp [v]; rw [hanchor]; exact floor_remainder_lt hM
    have hlen : (p.length : ℤ) ≤ ((t + 1) * 2 ^ h - 1 : ℕ) := by
      simp only [List.length_cons] at hplen
      omega
    have hB : (0 : ℤ) ≤
        (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ) := by positivity
    have hmult := mul_le_mul_of_nonneg_right hlen hB
    have hcast := retained_cast hf hz0 ⟨P, hP⟩
    change ((P.len - statePeriodModulus N ρ.length * deletionCounts z P : ℕ) : ℤ) =
        v ⟨P, hP⟩ at hcast
    have hcap : ((pieceLengthBound N ρ.length h t : ℕ) : ℤ) =
        fixedMargin N ρ.length + statePeriodModulus N ρ.length + ((t + 1) * 2 ^ h - 1 : ℕ) *
          (comparisonGap N ρ.length + statePeriodModulus N ρ.length :
              ℕ) := by simp [pieceLengthBound]
    omega
end DeciSigma1.Holes.Periodic
