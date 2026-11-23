-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Ph_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:08.090299+00:00
-- url     : https://prove2.me/submissions/3678a656-ee94-49a7-b0a6-28dcc9cdff2c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (h : p0 + p1 = 1) (K : B) : Ph p0 p1 c K K = K := by
  simp only [Ph, sub_self, smul_zero, sub_zero, add_zero, ← add_mul, h, one_mul]
end Formalism.FourierDecayAlt.P.Fr11
