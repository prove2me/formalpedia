-- Prove2me | solution 1 for FairSelling.exists_bags
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:30.626266+00:00
-- url     : https://prove2.me/submissions/8c5fd1f0-7fc1-4323-a1b3-cd0a76ca7a77

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Theorems.Thm_FairSelling_exists_minimal_subset_sum
import Theorems.Thm_FairSelling_minimal_bag_le

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [DecidableEq G]
namespace FairSelling
theorem _root_.solution (f : G → ℝ) (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    ∀ (k : ℕ) (A : Finset G), (∀ g ∈ A, f g ≤ ε) → (k : ℝ) * (τ + ε) ≤ ∑ g ∈ A, f g →
      ∃ B : Fin k → Finset G, (∀ j, B j ⊆ A) ∧
        (∀ j j', j ≠ j' → Disjoint (B j) (B j')) ∧
        (∀ j, τ ≤ ∑ g ∈ B j, f g) ∧ (∀ j, ∑ g ∈ B j, f g ≤ τ + ε) := by
  intro k
  induction k with
  | zero =>
    intro A _ _
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0⟩
  | succ k ih =>
    intro A hsmall htotal
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hτε : τ ≤ ∑ g ∈ A, f g := by
      have : (1 : ℝ) * (τ + ε) ≤ ((k : ℝ) + 1) * (τ + ε) := by
        have : (0 : ℝ) ≤ τ + ε := by linarith
        nlinarith
      push_cast at htotal
      linarith
    obtain ⟨B₀, hB₀sub, hB₀ge, hB₀min⟩ := exists_minimal_subset_sum f τ A hτε
    have hB₀le : ∑ g ∈ B₀, f g ≤ τ + ε :=
      minimal_bag_le hτ hε (fun g hg => hsmall g (hB₀sub hg)) hB₀ge hB₀min
    have hrest : ∑ g ∈ A \ B₀, f g = (∑ g ∈ A, f g) - ∑ g ∈ B₀, f g := by
      rw [Finset.sum_sdiff_eq_sub hB₀sub]
    have hrestge : (k : ℝ) * (τ + ε) ≤ ∑ g ∈ A \ B₀, f g := by
      push_cast at htotal
      rw [hrest]
      nlinarith
    obtain ⟨B, hBsub, hBdisj, hBge, hBle⟩ :=
      ih (A \ B₀) (fun g hg => hsmall g (Finset.mem_sdiff.mp hg).1) hrestge
    refine ⟨Fin.cases B₀ B, ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀sub
      · intro j'
        simpa using (hBsub j').trans Finset.sdiff_subset
    · intro j j'
      refine Fin.cases ?_ ?_ j
      · refine Fin.cases ?_ ?_ j'
        · intro hne; exact absurd rfl hne
        · intro j₂ _
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact Finset.disjoint_left.mpr (fun x hx hx' =>
            (Finset.mem_sdiff.mp (hBsub j₂ hx')).2 hx)
      · intro j₁
        refine Fin.cases ?_ ?_ j'
        · intro _
          simp only [Fin.cases_zero, Fin.cases_succ]
          exact Finset.disjoint_left.mpr (fun x hx hx' =>
            (Finset.mem_sdiff.mp (hBsub j₁ hx)).2 hx')
        · intro j₂ hne
          simp only [Fin.cases_succ]
          exact hBdisj j₁ j₂ (fun h => hne (congrArg Fin.succ h))
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀ge
      · intro j'; simpa using hBge j'
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hB₀le
      · intro j'; simpa using hBle j'
end FairSelling
