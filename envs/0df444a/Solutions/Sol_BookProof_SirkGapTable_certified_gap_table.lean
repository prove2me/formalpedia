-- Prove2me | solution 1 for BookProof.SirkGapTable.certified_gap_table
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:39:01.048922+00:00
-- url     : https://prove2.me/submissions/919df669-1eeb-486a-9b4b-ecf359098156

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_table
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution {n : ℕ} (row : Fin n → CouplingCertificate)
    (T P : Fin n → E →ₗ[ℂ] E) (thetaE thetaO deltaE deltaO : Fin n → ℝ)
    (hgap : ∀ i, (row i).gap = thetaO i - thetaE i)
    (hwidth : ∀ i, (row i).width = deltaO i + deltaE i)
    (hEven : ∀ i, sectorGround (T i) (P i) 1 ≤ thetaE i + deltaE i)
    (hOdd : ∀ i, thetaO i - deltaO i ≤ sectorGround (T i) (P i) (-1)) :
    ∀ i, (row i).lo ≤ sectorGround (T i) (P i) (-1) - sectorGround (T i) (P i) 1 := by
  intro i
  unfold CouplingCertificate.lo
  rw [hgap i, hwidth i]
  linarith [hEven i, hOdd i]

#print axioms solution
