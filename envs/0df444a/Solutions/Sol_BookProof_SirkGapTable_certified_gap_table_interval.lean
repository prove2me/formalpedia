-- Prove2me | solution 1 for BookProof.SirkGapTable.certified_gap_table_interval
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:12:21.276161+00:00
-- url     : https://prove2.me/submissions/a6d3429c-e62b-4550-958a-bbf019300460

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_table_interval
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
    (hEvenHi : ∀ i, sectorGround (T i) (P i) 1 ≤ thetaE i + deltaE i)
    (hEvenLo : ∀ i, thetaE i - deltaE i ≤ sectorGround (T i) (P i) 1)
    (hOddLo : ∀ i, thetaO i - deltaO i ≤ sectorGround (T i) (P i) (-1))
    (hOddHi : ∀ i, sectorGround (T i) (P i) (-1) ≤ thetaO i + deltaO i) :
    ∀ i, sectorGround (T i) (P i) (-1) - sectorGround (T i) (P i) 1
        ∈ Set.Icc (row i).lo (row i).hi := by
  intro i
  constructor
  · change (row i).gap - (row i).width ≤ _
    rw [hgap i, hwidth i]
    linarith [hEvenHi i, hOddLo i]
  · change _ ≤ (row i).gap + (row i).width
    rw [hgap i, hwidth i]
    linarith [hEvenLo i, hOddHi i]

#print axioms solution
