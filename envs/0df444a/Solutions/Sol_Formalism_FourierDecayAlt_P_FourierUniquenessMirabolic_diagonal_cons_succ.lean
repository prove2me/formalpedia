-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic.diagonal_cons_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:51.769573+00:00
-- url     : https://prove2.me/submissions/d21e03db-2a2b-43cd-93fe-059a1b651745

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
theorem _root_.solution {n : ℕ} (a b : ℂ) (x : Fin n → ℂ) (i : Fin n) (j : Fin (n + 1)) :
    Matrix.diagonal (Fin.cons a x : Fin (n + 1) → ℂ) i.succ j =
      Matrix.diagonal (Fin.cons b x : Fin (n + 1) → ℂ) i.succ j := by
  simp only [Matrix.diagonal_apply, Fin.cons_succ]
end Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
