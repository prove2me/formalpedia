-- Prove2me | solution 1 for BookProof.HermiteBand.IsBand2.add
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:35.109328+00:00
-- url     : https://prove2.me/submissions/2b7ccc69-b0d5-4d44-ad87-34df4fc5350e

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

theorem solution {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBand2 T) (hS : IsBand2 S) : IsBand2 (T + S) := by
  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hS
  exact ⟨M₁ + M₂, C₁ + C₂, add_nonneg hC₁ hC₂, band_add h₁ h₂⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
