-- Prove2me | solution 1 for ChvatalOneHard398.SAT.latticeFormula_satisfiable_iff_candidates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:50:00.788881+00:00
-- url     : https://prove2.me/submissions/a6a6c679-9681-44f9-9bad-c7467911b341
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding
import Theorems.Thm_ChvatalOneHard398_SAT_proposition_16

open scoped BigOperators
open ChvatalOneHard398.SAT

theorem solution
    (a : ChvatalOneHard398.SAT.Params) (ha : a.Valid) :
    ChvatalOneHard398.SAT.Satisfiable (ChvatalOneHard398.SAT.latticeFormula a) ↔
      ∃ y : Fin a.m → ℤ, y ∈ ChvatalOneHard398.SAT.congruenceKernel a.D a.H ∧
        ∀ i, -((2 : ℤ)^(a.h-1)-1) ≤ a.t i-y i ∧
          a.t i-y i ≤ (2 : ℤ)^(a.h-1) := by
  obtain ⟨e⟩ := (proposition_16.2 a ha).2.2.1
  constructor
  · rintro ⟨assignment, hassignment⟩
    let y : candidateVectors a := e ⟨assignment, hassignment⟩
    exact ⟨y.1, y.2.1, y.2.2⟩
  · rintro ⟨y, hyM, hybox⟩
    let y' : candidateVectors a := ⟨y, hyM, hybox⟩
    let assignment : assignments (latticeFormula a) := e.symm y'
    exact ⟨assignment.1, assignment.2⟩
