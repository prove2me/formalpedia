-- Prove2me | solution 1 for Formalism.H.unfolding_fourier_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.278844+00:00
-- url     : https://prove2.me/submissions/c1cf73fa-43c1-4eda-91b4-9e7b55e53326

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Theorems.Thm_Formalism_H_unfoldCoeff_main

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
theorem _root_.solution (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : UnfoldCoeff V := by
  intro Λ _ _ f hf D hD μ hμ
  exact unfoldCoeff_main Λ f hf D hD μ hμ
end Formalism.H
