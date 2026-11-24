-- Prove2me | solution 1 for Formalism.H.gaussian_fourier_transform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:06.932505+00:00
-- url     : https://prove2.me/submissions/9a0a4b84-6f79-4105-b8b1-2b189208aa27

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Theorems.Thm_Formalism_H_gauss_continuous
import Theorems.Thm_Formalism_H_gauss_decay
import Theorems.Thm_Formalism_H_gauss_fourier

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
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution : GaussFourier V := fun t ht => ⟨gauss_continuous V t, gauss_decay V t ht, gauss_fourier V t ht⟩
end Formalism.H
