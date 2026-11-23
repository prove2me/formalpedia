-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.freeOf_diagScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:48.084074+00:00
-- url     : https://prove2.me/submissions/dbb4b17d-d785-4145-b12c-1437a5df0d60

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_zero

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
theorem _root_.solution {a : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf a b) : FreeOf2 a (d0 b) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa [d0] using h
  · simpa [d0, hij] using free_zero (A := A) a
end Formalism.FourierDecayAlt.P.Wd9
