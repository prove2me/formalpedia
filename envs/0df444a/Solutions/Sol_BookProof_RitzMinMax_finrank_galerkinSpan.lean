-- Prove2me | solution 1 for BookProof.RitzMinMax.finrank_galerkinSpan
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:46:49.31875+00:00
-- url     : https://prove2.me/submissions/1e37d6d0-8f96-4f38-b498-24c544adcdef

-- Generated from ChapterSirkRitzMinMax.lean — solution of BookProof.RitzMinMax.finrank_galerkinSpan
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax










noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    Module.finrank ℂ (galerkinSpan b m) = m := by

  classical
  have hrange : Set.range (fun i : Fin m => b i.val) = b '' {i | i < m} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hli : LinearIndependent ℂ (fun i : Fin m => b i.val) :=
    b.orthonormal.linearIndependent.comp _ Fin.val_injective
  rw [galerkinSpan, ← hrange, finrank_span_eq_card hli]
  simp
