-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Ph_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:51.944098+00:00
-- url     : https://prove2.me/submissions/68d9555d-91ad-4cdf-8b70-c360bdbfd563

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
theorem _root_.solution (U V U' V' : B) : Ph p0 p1 c (U + U') (V + V') = Ph p0 p1 c U V + Ph p0 p1 c U' V' := by
  unfold Ph
  rw [add_sub_add_comm, smul_add]
  simp only [mul_add, mul_sub]
  abel
end Formalism.FourierDecayAlt.P.Fr11
