-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_real_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:32.869973+00:00
-- url     : https://prove2.me/submissions/98d31387-c0ac-4773-8c99-3b90d63f800d

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ)
    (hg : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) (n : ℕ) :
    0 ≤ (avg e c g n).re ∧ (avg e c g n).im = 0 := by
  unfold avg
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.re_sum, Complex.im_sum]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun m _ => (hg _).1))
  · simp [(hg _).2]
end Formalism.FourierDecayAlt.P.BoxAverageLimits
