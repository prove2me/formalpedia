-- Prove2me | solution 1 for BookProof.ChapterSuperBracket.sbracket_even_left
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-14T09:06:19.946493+00:00
-- url     : https://prove2.me/submissions/3115cb72-9c79-4d3f-8750-a96066f2eaad

-- Generated from ChapterSuperBracket.lean — theorem BookProof.ChapterSuperBracket.sbracket_even_left
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket



variable {R : Type*} [Ring R]

theorem solution (q : Bool) (a b : R) : sbracket false q a b = a * b - b * a := by
  cases q <;> simp [BookProof.ChapterSuperBracket.sbracket, BookProof.ChapterSuperBracket.eps]

#print axioms solution
