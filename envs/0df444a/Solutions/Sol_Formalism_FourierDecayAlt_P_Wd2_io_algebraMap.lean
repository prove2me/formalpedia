-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.io_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:55.994146+00:00
-- url     : https://prove2.me/submissions/1603a0fe-f815-467e-9599-0a7b8cc3f7a0

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
theorem _root_.solution (c : K) : (io (algebraMap K A c) : SlopeTestRemainingChoices S A) = algebraMap K (SlopeTestRemainingChoices S A) c := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
    Pi.algebraMap_apply]
end Formalism.FourierDecayAlt.P.Wd2
