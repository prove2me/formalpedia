-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.mem_perp_spanC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:43.504861+00:00
-- url     : https://prove2.me/submissions/d987b926-3a32-4083-9d3c-06e8dc02fb15

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_add
import Theorems.Thm_CompanionTheory_D_gk_RF_Lowers_smul
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_add_leftC
import Theorems.Thm_CompanionTheory_D_gk_RF_hf_smul_leftC

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
theorem _root_.solution {ι : Type} {w : ι → Fin n → K} {z : Fin n → K} (h : ∀ i, hf J (w i) z = 0) :
    z ∈ perp J (Submodule.span K (Set.range w)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_leftC, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_leftC, ha, mul_zero]
end CompanionTheory.D.gk.RF
