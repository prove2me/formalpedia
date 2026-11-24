-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.partial_flip_mul_J_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:39.977613+00:00
-- url     : https://prove2.me/submissions/25036d98-1af1-4cea-9e7c-4240bd74f7c6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_mul_eU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (a : S) : Q0 a * d0 (ins a JJ) = d0 (ins a JJ) * (1 - P0 a) := by
  ext i j
  rw [d0, Matrix.diagonal_mul, Matrix.mul_diagonal, ins_J]
  fin_cases i <;> fin_cases j <;>
    simp [P0, Q0, mul_sub, sub_mul, Wd1.eU_mul_eU]
end Formalism.FourierDecayAlt.P.Wd9
