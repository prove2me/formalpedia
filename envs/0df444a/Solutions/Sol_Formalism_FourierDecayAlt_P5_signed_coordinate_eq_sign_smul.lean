-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:50:41.212378+00:00
-- url     : https://prove2.me/submissions/a1b18faa-4aca-48aa-9d1e-63e7e3c3f78d

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignedCoordinateEqSignSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (P : M.Par) (l : ℕ) (Y : ℂ) :
    (fun ρ => M.x0 P l ρ Y) = M.sgn P l • fun ρ => M.xC P ρ Y := by
  funext ρ
  simp only [Pi.smul_apply, smul_eq_mul, M.x0, M.sgn, M.xC]
end Formalism.FourierDecayAlt.P5
