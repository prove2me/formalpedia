-- Prove2me | solution 1 for BookProof.HermiteBand.Band.add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:22.965306+00:00
-- url     : https://prove2.me/submissions/522a48a5-5ddc-4282-b0fe-6b635cf6736b

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.Band.add
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M₁ M₂ : ℕ}
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
