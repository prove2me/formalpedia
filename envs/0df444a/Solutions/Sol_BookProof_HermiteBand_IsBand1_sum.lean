-- Prove2me | solution 1 for BookProof.HermiteBand.IsBand1.sum
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:33.707064+00:00
-- url     : https://prove2.me/submissions/c67c0258-1d37-4e7f-a555-7f638ba7afa0

/-
Adapted from leonardopedro/timepiece, ChapterHermiteBandCalculus.lean,
commit 61595bca99e3b8d8b8df51a2c3043b64597e24f9 (Apache-2.0).
Helper proofs, where needed, are included directly; no platform theorem imports.
-/
import Definitions.Def_ChapterHermiteBandCalculus

open BookProof.HermiteBand
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem band_add {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M₁ M₂ : ℕ}
    {C₁ C₂ : ℝ} {g : ℕ → ℝ}
    (hT : Band T r M₁ C₁ g) (hS : Band S r M₂ C₂ g) :
    Band (T + S) r (M₁ + M₂) (C₁ + C₂) g := by
  classical
  intro α
  obtain ⟨f₁, hrep₁, hcard₁, hband₁, hcoef₁⟩ := hT α
  obtain ⟨f₂, hrep₂, hcard₂, hband₂, hcoef₂⟩ := hS α
  refine ⟨f₁ + f₂, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.add_apply, hrep₁, hrep₂, hcomb, map_add]
  · calc (f₁ + f₂).support.card ≤ (f₁.support ∪ f₂.support).card :=
          Finset.card_le_card Finsupp.support_add
      _ ≤ f₁.support.card + f₂.support.card := Finset.card_union_le _ _
      _ ≤ M₁ + M₂ := Nat.add_le_add hcard₁ hcard₂
  · intro β hβ
    rcases Finset.mem_union.mp (Finsupp.support_add hβ) with h | h
    · exact hband₁ β h
    · exact hband₂ β h
  · intro β
    refine le_trans (norm_add_le _ _) ?_
    have := hcoef₁ β
    have := hcoef₂ β
    nlinarith

private theorem band_closed_add {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBand1 T) (hS : IsBand1 S) : IsBand1 (T + S) := by
  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hS
  exact ⟨M₁ + M₂, C₁ + C₂, add_nonneg hC₁ hC₂, band_add h₁ h₂⟩

private theorem band_zero :
    IsBand1 (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  refine ⟨0, 0, le_refl 0, fun α => ⟨0, ?_, ?_, ?_, ?_⟩⟩
  · simp [hcomb]
  · simp
  · simp
  · simp

theorem solution {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBand1 (F i)) : IsBand1 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using band_zero (d := d)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact band_closed_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
