-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.isCompact_preimage_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:03.965216+00:00
-- url     : https://prove2.me/submissions/ac91cba2-6f92-43e4-a25d-7091dd3e6b7d

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
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {Q : Set ℂ} (hQ : IsCompact Q) :
    IsCompact {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by
  have hcont : Continuous fun z : ℂ => ε⁻¹ * z ^ s := by fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (hQ.isClosed.preimage hcont) ?_
  obtain ⟨M, hM⟩ := hQ.isBounded.exists_norm_le
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 M)).subset fun z hz => ?_
  have h1 : ‖z‖ ^ s ≤ M := by
    have := hM _ hz
    rwa [norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow] at this
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  have h2 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h3 : ‖z‖ ≤ ‖z‖ ^ s := le_self_pow₀ h2.le hs
  linarith [le_max_right 1 M]
end Formalism.FourierDecayAlt.P.PBK
