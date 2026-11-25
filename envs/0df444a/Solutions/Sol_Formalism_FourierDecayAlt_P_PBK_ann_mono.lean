-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.ann_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:32:54.901556+00:00
-- url     : https://prove2.me/submissions/8d13d7d9-9da2-4695-931f-250f21c2a8a5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution : Monotone ann := by
  intro m n hmn D hD
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩
end Formalism.FourierDecayAlt.P.PBK
