-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx9.star_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:33.388657+00:00
-- url     : https://prove2.me/submissions/01a73f86-73c4-4bbc-943b-43265c822cf8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9
namespace Formalism.FourierDecayAlt.P.Mx9
theorem _root_.solution {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h
end Formalism.FourierDecayAlt.P.Mx9
