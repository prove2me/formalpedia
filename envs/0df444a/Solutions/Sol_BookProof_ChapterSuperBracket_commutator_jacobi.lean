-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.commutator_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-14T09:07:51.910528+00:00
-- url     : https://prove2.me/submissions/5de03a39-d1df-45f7-9156-fd0cdaaa249d

-- Generated from ChapterSuperBracket.lean — theorem BookProof.ChapterSuperBracket.commutator_jacobi
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket



variable {R : Type*} [Ring R]

theorem solution (a b c : R) :
    sbracket false false a (sbracket false false b c)
  + sbracket false false b (sbracket false false c a)
  + sbracket false false c (sbracket false false a b) = 0 := by
  simp [BookProof.ChapterSuperBracket.sbracket, BookProof.ChapterSuperBracket.eps]
  noncomm_ring

#print axioms solution
