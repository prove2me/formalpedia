-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:19:39.25351+00:00
-- url     : https://prove2.me/submissions/e3b1c12a-7f3c-4f36-a488-7f84163e0a09

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Produce the global Lipschitz exponent from the actual bounded total gradient. -/
theorem solution {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x)) := by
  have hgrad_bound (x : EuclideanSpace ℝ (Fin n)) :
      ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ))
      hV.locallyLipschitz.locallyLipschitzOn
  have hmaps : MapsTo (gradient u) univ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)) := by
    intro x _
    simpa only [mem_closedBall, dist_zero_right] using hgrad_bound x
  have hcomp : LipschitzWith (C * G) (V ∘ gradient u) :=
    lipschitzOnWith_univ.mp (hC.comp hG.lipschitzOnWith hmaps)
  exact ⟨L + C * G, hL.neg.add hcomp⟩
