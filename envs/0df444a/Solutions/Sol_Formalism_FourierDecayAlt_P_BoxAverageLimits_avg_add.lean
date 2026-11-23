-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:18.659922+00:00
-- url     : https://prove2.me/submissions/ec090ee2-7489-4cbf-a4cf-0a820c2d1f6b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g h : Λ → ℂ) :
    avg e c (g + h) = avg e c g + avg e c h := by
  funext n; simp [avg, Finset.sum_add_distrib, mul_add]
end Formalism.FourierDecayAlt.P.BoxAverageLimits
