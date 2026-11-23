-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.hess_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.809269+00:00
-- url     : https://prove2.me/submissions/90fafc46-f90c-4201-b3a8-25e01a1d27d4

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution (m : ℕ) (z t : Kˣ) :
    hessM m (z * t) = ((t⁻¹ : Kˣ) : K) • hessM m z := by
  unfold hessM
  rw [smul_smul, mul_inv, Units.val_mul, mul_comm]
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
