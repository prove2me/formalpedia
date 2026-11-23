-- Prove2me | solution 1 for Formalism.H.schwartz_decay_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:16.665897+00:00
-- url     : https://prove2.me/submissions/b80cbb7c-0f99-48bc-b0cf-89199dfd351f

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz

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
theorem _root_.solution : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h
end Formalism.H
