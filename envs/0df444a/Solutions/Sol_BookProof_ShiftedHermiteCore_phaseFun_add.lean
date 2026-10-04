-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.phaseFun_add
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:34:02.583289+00:00
-- url     : https://prove2.me/submissions/866a2b9c-84db-4583-8dc9-733bb61ae9bd

/-
Adapted from leonardopedro/timepiece, ChapterShiftedHermiteCore.lean,
commit 61595bca99e3b8d8b8df51a2c3043b64597e24f9 (Apache-2.0).
-/
import Definitions.Def_ChapterShiftedHermiteCore

open BookProof.ShiftedHermiteCore BookProof.HermiteProductCore
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem solution (k x y : Vd d) : phaseFun k (x + y) = phaseFun k x * phaseFun k y := by
  rw [phaseFun, phaseFun, phaseFun, ← Complex.exp_add]
  congr 1
  have : phaseArg k (x + y) = phaseArg k x + phaseArg k y := by
    simp only [phaseArg, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_add]
  rw [this]
  push_cast
  ring

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
