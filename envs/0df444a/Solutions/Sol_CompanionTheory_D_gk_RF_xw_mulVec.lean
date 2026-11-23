-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.xw_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:34.623255+00:00
-- url     : https://prove2.me/submissions/f475d16e-cc75-4e56-8c72-6cefd15a9d65

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
namespace CompanionTheory.D.gk.RF
theorem _root_.solution (w b z : Fin n → K) : xw J w b *ᵥ z = hf J b z • w - hf J w z • b := by
  simp only [xw, sub_mulVec, vecMulVec_mulVec, hf, dotProduct_mulVec, op_smul_eq_smul]
end CompanionTheory.D.gk.RF
