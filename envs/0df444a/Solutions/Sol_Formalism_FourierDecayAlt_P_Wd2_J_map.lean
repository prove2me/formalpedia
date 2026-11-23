-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.J_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:27.349924+00:00
-- url     : https://prove2.me/submissions/c70ed059-1609-4d69-a1b9-8e8c867e4077

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))
end Formalism.FourierDecayAlt.P.Wd2
