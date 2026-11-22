-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.eU_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:41.205935+00:00
-- url     : https://prove2.me/submissions/162684d3-dd64-4ba9-9a5c-7b241345e2d7

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show (eU a i j : SlopeTestRemainingChoices S A) * io x = io x * eU a i j
  unfold io
  ext X Y
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd6
