-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.symm_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:25.365726+00:00
-- url     : https://prove2.me/submissions/1746dd26-9f25-40ae-b66c-6143195ff6f2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i
end Formalism.FourierDecayAlt.P.G5
