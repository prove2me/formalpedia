-- Prove2me | solution 1 for D1Bound5.halfOffDiagonalInverse_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:29.053814+00:00
-- url     : https://prove2.me/submissions/9d5c4d6d-83d0-4b89-867a-9ae5d1d1975e

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ReferenceInverseNorm_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Theorems.Thm_D1Bound5_halfOffDiagonalInverse_mul_reflection_plus_one

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5















theorem _root_.solution :
    2 ≤ ‖halfOffDiagonalInverse‖ := by
  let Q : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 : Matrix (Fin 4) (Fin 4) ℂ) + referenceReflection
  have hQ : Q ≠ 0 := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
    norm_num [Q, referenceReflection] at h00
  have hQpos : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  have hKQ : halfOffDiagonalInverse * Q = (-2 : ℂ) • Q :=
    halfOffDiagonalInverse_mul_reflection_plus_one
  have hmul := Matrix.l2_opNorm_mul halfOffDiagonalInverse Q
  rw [hKQ, norm_smul] at hmul
  have hn : ‖(-2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [hn] at hmul
  by_contra hbad
  have hdiff : 0 < 2 - ‖halfOffDiagonalInverse‖ := sub_pos.mpr (lt_of_not_ge hbad)
  have hprod := mul_pos hdiff hQpos
  nlinarith only [hmul, hprod]





end D1Bound5
end
