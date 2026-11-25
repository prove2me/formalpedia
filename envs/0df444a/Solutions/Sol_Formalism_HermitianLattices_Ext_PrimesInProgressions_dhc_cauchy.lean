-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhc_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:52.957486+00:00
-- url     : https://prove2.me/submissions/c77251bb-fdc4-4e64-b171-e3f9e6ff173b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (H : ℂ → ℂ) (z₀ s : ℂ) (ϱ C : ℝ) (hϱ : 0 < ϱ)
    (hHd : DifferentiableOn ℂ H (Metric.ball z₀ (2 * ϱ))) (hHb : ∀ z ∈ Metric.ball z₀ (2 * ϱ), ‖H z‖ ≤ C)
    (hs : s ∈ Metric.closedBall z₀ ϱ) (k : ℕ) :
    ‖iteratedDeriv k H s‖ ≤ k.factorial * C / ϱ ^ k := by
  have hcont : ContinuousAt (fun R : ℝ => (k.factorial : ℝ) * C / R ^ k) ϱ :=
    continuousAt_const.div (continuousAt_id.pow k) (pow_pos hϱ k).ne'
  have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ϱ))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hϱ] with R hR
  have hsub : Metric.closedBall s R ⊆ Metric.ball z₀ (2 * ϱ) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz hs
    rw [Metric.mem_ball]
    have := dist_triangle z s z₀
    linarith [hR.2]
  exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR.1 (hHd.diffContOnCl_ball hsub)
    (fun z hz => hHb z (hsub (Metric.sphere_subset_closedBall hz)))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
