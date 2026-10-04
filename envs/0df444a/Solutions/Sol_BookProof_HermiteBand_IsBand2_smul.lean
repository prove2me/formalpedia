-- Prove2me | solution 1 for BookProof.HermiteBand.IsBand2.smul
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:36.609599+00:00
-- url     : https://prove2.me/submissions/ca33f656-02ec-48e3-affd-1d74387b2903

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

private theorem band_smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M : ℕ}
    {C : ℝ} {g : ℕ → ℝ} (c : ℂ) (h : Band T r M C g) :
    Band (c • T) r M (‖c‖ * C) g := by
  classical
  intro α
  obtain ⟨f, hrep, hcard, hband, hcoef⟩ := h α
  refine ⟨c • f, ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hrep, hcomb, map_smul]
  · exact le_trans (Finset.card_le_card (Finsupp.support_smul)) hcard
  · intro β hβ
    exact hband β (Finsupp.support_smul hβ)
  · intro β
    have h1 : ‖(c • f) β‖ = ‖c‖ * ‖f β‖ := by
      simp [Finsupp.smul_apply]
    rw [h1, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcoef β) (norm_nonneg c)

theorem solution {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ)
    (hT : IsBand2 T) : IsBand2 (c • T) := by
  obtain ⟨M, C, hC, h⟩ := hT
  exact ⟨M, ‖c‖ * C, mul_nonneg (norm_nonneg c) hC, band_smul c h⟩

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
