-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:33.62316+00:00
-- url     : https://prove2.me/submissions/130e00ab-3afd-4e36-9f51-943ebf9253f0

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {p q : Fin 4 → ℝ} (h : hermOfMom p = hermOfMom q) :
    ∀ i, p i = q i := by

  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  simp only [hermOfMom, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] at h00 h11 h01
  have e0 : p 0 + p 3 = q 0 + q 3 := by exact_mod_cast congrArg Complex.re h00
  have e1 : p 0 - p 3 = q 0 - q 3 := by exact_mod_cast congrArg Complex.re h11
  have e2 : p 1 = q 1 := by
    have := congrArg Complex.re h01
    simpa using this
  have e3 : p 2 = q 2 := by
    have := congrArg Complex.im h01
    simp at this
    linarith
  intro i
  fin_cases i
  · simpa using (by linarith : p 0 = q 0)
  · simpa using e2
  · simpa using e3
  · simpa using (by linarith : p 3 = q 3)
