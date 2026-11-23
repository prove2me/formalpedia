-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.151885+00:00
-- url     : https://prove2.me/submissions/db3189a6-9ca0-4bc4-af70-06dd191e1a84

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (a : ℂ) (g : Λ → ℂ) :
    avg e c (a • g) = fun n => a * avg e c g n := by
  funext n; simp only [avg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring
end Formalism.FourierDecayAlt.P.BoxAverageLimits
