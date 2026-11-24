-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.dot_self_eq_sq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:56.179735+00:00
-- url     : https://prove2.me/submissions/322c51ad-e8d0-4d1a-8100-5e3d0f1dbefb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DotSelfEqSqNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open Matrix
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [dotProduct, sq]
end Formalism.L2.Pj.FundamentalDomainD5
