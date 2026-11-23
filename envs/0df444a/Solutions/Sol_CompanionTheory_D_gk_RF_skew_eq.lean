-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.skew_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:44.525606+00:00
-- url     : https://prove2.me/submissions/6d1f3123-2e64-4090-8554-a6f3ab6641c0

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
variable [CharZero K]
omit [CharZero K]
namespace CompanionTheory.D.gk.RF
theorem _root_.solution {X : Matrix (Fin n) (Fin n) K} (h : Xᴴ * J + J * X = 0) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left h
end CompanionTheory.D.gk.RF
