-- Prove2me | solution 1 for Formalism.H.thetaPos_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:53.57761+00:00
-- url     : https://prove2.me/submissions/30018578-e926-4865-9c8c-03268d32bfe5

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (hS : ThetaSummable V) : ThetaPos V := by
  intro Λ _ _ t ht
  have hs := hS Λ t ht 0
  simp only [add_zero] at hs
  have := hs.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  simpa [theta] using this
end Formalism.H
