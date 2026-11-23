-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Ph_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:08.125254+00:00
-- url     : https://prove2.me/submissions/e401f3b0-59ef-43d1-a264-cd91e6963e85

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
theorem _root_.solution (U V U' V' : B) : Ph p0 p1 c (U - U') (V - V') = Ph p0 p1 c U V - Ph p0 p1 c U' V' := by
  unfold Ph
  rw [sub_sub_sub_comm, smul_sub]
  simp only [mul_add, mul_sub]
  abel
end Formalism.FourierDecayAlt.P.Fr11
