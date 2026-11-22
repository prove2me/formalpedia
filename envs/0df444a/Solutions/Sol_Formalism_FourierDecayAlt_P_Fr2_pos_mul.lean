-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.pos_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:23.357641+00:00
-- url     : https://prove2.me/submissions/9ce72d73-5169-46a7-9ab4-16c4ab3ae1f3

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
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a * b) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_re, a2, b2]; positivity
  · simp [Complex.mul_im, a2, b2]
end Formalism.FourierDecayAlt.P.Fr2
