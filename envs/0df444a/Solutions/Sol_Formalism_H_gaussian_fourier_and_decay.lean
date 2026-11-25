-- Prove2me | solution 1 for Formalism.H.gaussian_fourier_and_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:49:43.086993+00:00
-- url     : https://prove2.me/submissions/7f081659-23d5-4ca5-8ae6-05db187bba01

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Theorems.Thm_Formalism_H_gaussian_fourier_transform
import Theorems.Thm_Formalism_H_schwartz_decay_gaussian

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
theorem _root_.solution : GaussFourier V ∧ SchwartzDecay V := ⟨gaussian_fourier_transform V, schwartz_decay_gaussian V⟩
end Formalism.H
