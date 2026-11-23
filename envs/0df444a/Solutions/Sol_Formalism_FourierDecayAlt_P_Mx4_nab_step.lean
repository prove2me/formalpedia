-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.nab_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:50.538403+00:00
-- url     : https://prove2.me/submissions/8ca88132-d43c-4ec6-b7ea-51b6f7f33059

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (a : ℝ) (D W : Pr r) (c : ℂ) :
    (D + ((a - 1 : ℝ) : ℂ) • W) * algebraMap ℂ (Pr r) c =
      algebraMap ℂ (Pr r) c * (D + (a : ℂ) • W) - W * algebraMap ℂ (Pr r) c := by
  rw [Algebra.commutes c (D + (a : ℂ) • W), ← sub_mul]
  congr 1
  push_cast
  rw [sub_smul, one_smul]
  abel
end Formalism.FourierDecayAlt.P.Mx4
