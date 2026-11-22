-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.additive_character_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:08.414829+00:00
-- url     : https://prove2.me/submissions/a15d1801-1294-40f3-bd55-092d48ba4699

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi

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
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PsiChar := by
  intro β x y
  refine ⟨?_, ?_, ?_⟩
  · simp [psi, mul_add, Complex.exp_add]
  · simp only [psi]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  · simp [psi]
end Formalism.FourierDecayAlt.P
