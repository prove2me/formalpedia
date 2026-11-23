-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.skew_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:26.861772+00:00
-- url     : https://prove2.me/submissions/b65a8a33-23d5-4388-8f37-9628f0de9417

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_skew_eq

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
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) K} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y)ᴴ * J = J * (Y * X) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, skew_eq hX, Matrix.mul_neg, ← Matrix.mul_assoc, skew_eq hY,
    Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
end CompanionTheory.D.gk.RF
