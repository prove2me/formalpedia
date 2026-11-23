-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realCharacter_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.677791+00:00
-- url     : https://prove2.me/submissions/caea85c5-cdbf-4bda-80f0-1c8e9ef9c61f

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : RealCharacter := by
  unfold RealCharacter
  intro g rd x hg hrd
  have hg' : (g:ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hrd' : (rd:ℂ) ≠ 0 := by exact_mod_cast hrd.ne'
  congr 1
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp
  try ring
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
