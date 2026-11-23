-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.q_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:58.620954+00:00
-- url     : https://prove2.me/submissions/a808313e-d106-4a48-9da7-1e3be5872ce0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) : (ofWord L st w).q = qw st.q w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    by_cases hp : l.plus
    · funext Y; simp [ofWord, qw, hp, FrameData.plus, ih]
    · funext Y; simp [ofWord, qw, hp, FrameData.minus, ih]
end Formalism.FourierDecayAlt.P.Fr2
