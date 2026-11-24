-- Prove2me | solution 1 for FairSelling.exists_minimal_bag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:58.203749+00:00
-- url     : https://prove2.me/submissions/75ad67f2-50bc-4fec-a310-e35116e8cd6c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
open Classical
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    (T : Finset (Fin n)) (R : Finset G) (D : ℝ)
    (hsmall : ∀ i ∈ T, ∀ g ∈ R, vbar (v i) p g < τ i)
    (hD : ∀ i ∈ T, D < τ i)
    (j₀ : Fin n) (hj₀ : j₀ ∈ T) (hfull : τ j₀ ≤ vbarSum (v j₀) p R + D) :
    ∃ (B : Finset G) (j : Fin n), B ⊆ R ∧ j ∈ T ∧
      τ j ≤ vbarSum (v j) p B + D ∧
      ∀ i ∈ T, vbarSum (v i) p B + D < 2 * τ i := by
  classical
  set S := R.powerset.filter (fun B => ∃ i ∈ T, τ i ≤ vbarSum (v i) p B + D) with hSdef
  have hRS : R ∈ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl R, ⟨j₀, hj₀, hfull⟩⟩
  obtain ⟨B, hBS, hBmin⟩ := Finset.exists_min_image S Finset.card ⟨R, hRS⟩
  have hBR : B ⊆ R := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset] at hBS; exact hBS.1
  obtain ⟨j, hjT, hjB⟩ : ∃ i ∈ T, τ i ≤ vbarSum (v i) p B + D := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_powerset] at hBS; exact hBS.2
  have hBne : B.Nonempty := by
    rcases Finset.eq_empty_or_nonempty B with h | h
    · exfalso
      rw [h] at hjB
      simp only [vbarSum, Finset.sum_empty, zero_add] at hjB
      exact absurd hjB (not_le.mpr (hD j hjT))
    · exact h
  obtain ⟨g, hgB⟩ := hBne
  have hgR : g ∈ R := hBR hgB
  have herase : B.erase g ∉ S := by
    intro hmem
    have := hBmin _ hmem
    have hlt : (B.erase g).card < B.card := Finset.card_erase_lt_of_mem hgB
    omega
  have hno : ∀ i ∈ T, vbarSum (v i) p (B.erase g) + D < τ i := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    exact herase (by
      simp only [hSdef, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.trans (Finset.erase_subset _ _) hBR, ⟨i, hi, hcon⟩⟩)
  refine ⟨B, j, hBR, hjT, hjB, ?_⟩
  intro i hi
  have hsplit : vbarSum (v i) p B = vbarSum (v i) p (B.erase g) + vbar (v i) p g := by
    unfold vbarSum
    rw [← Finset.sum_erase_add B _ hgB]
  have h1 := hno i hi
  have h2 := hsmall i hi g hgR
  linarith [hsplit]
end FairSelling
