-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.second_order_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:31.705568+00:00
-- url     : https://prove2.me/submissions/8a60ec8a-92e3-4b65-913a-5c767f9b2961

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_triple

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
namespace CompanionTheory.D.gk.RF
theorem _root_.solution {X Y : Matrix (Fin n) (Fin n) K} (hX : Lowers J W X) (hY : Lowers J W Y) :
    ex2 X * ex2 Y = 1 + X + Y + (2 : K)⁻¹ • (X * X) + X * Y + (2 : K)⁻¹ • (Y * Y) := by
  have t1 := hX.triple hX hY
  have t2 := hX.triple hY hY
  simp only [ex2, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, t1, t2, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, smul_zero, add_zero]
  abel
end CompanionTheory.D.gk.RF
