-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.phaseFun_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:12:01.332818+00:00
-- url     : https://prove2.me/submissions/22139d49-f052-4d5d-916c-da0404f44e00

import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore

open BookProof.HermiteProductCore BookProof.ShiftedHermiteCore

-- Adapted from leonardopedro/timepiece, ChapterShiftedHermiteCore.lean, Apache-2.0.
theorem solution {d : ℕ} (k x : Vd d) : phaseFun k x ≠ 0 :=
  Complex.exp_ne_zero _

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
