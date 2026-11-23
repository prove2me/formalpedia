-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.key_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:27.123116+00:00
-- url     : https://prove2.me/submissions/aaeaee83-3e1d-4302-87d2-26742a198d35

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' : B) (Y Y' Ya : ℂ) (hne : Y ≠ Y')
    (H1 : (Y - Y') • (t * b' - b' * t) = t * b' - t' * b)
    (H2 : (Y' - Y) • (t' * b - b * t') = t' * b - t * b') :
    (Y - Ya - 1) • (b * t') + (Y' - Ya) • (t * b') = (Y' - Ya - 1) • (b' * t) + (Y - Ya) • (t' * b) := by
  have hS : (Y - Y') • (b * t' + t * b' - b' * t - t' * b) = 0 := by
    linear_combination (norm := module) H1 + H2
  have hS0 : b * t' + t * b' - b' * t - t' * b = 0 :=
    (smul_eq_zero.mp hS).resolve_left (sub_ne_zero.mpr hne)
  linear_combination (norm := module) (Y' - Ya - 1) • hS0 + H2
end Formalism.FourierDecayAlt.P.Fr7
