-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:38.813262+00:00
-- url     : https://prove2.me/submissions/d0cdac21-a369-4345-b69c-3046a8a548e1

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_pos_ofReal

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
theorem _root_.solution (z : ℂ) (hz : z.im = 0) (a b : ℝ) (h : 0 < (z.re + a) * (z.re + b)) :
    Pos ((z + a) / (z + b)) := by
  have e : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [e, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_div]
  apply pos_ofReal
  have hb : z.re + b ≠ 0 := by intro h0; simp [h0] at h
  have : (z.re + a) / (z.re + b) = (z.re + a) * (z.re + b) / (z.re + b) ^ 2 := by
    field_simp
  rw [this]; positivity
end Formalism.FourierDecayAlt.P.Fr2
