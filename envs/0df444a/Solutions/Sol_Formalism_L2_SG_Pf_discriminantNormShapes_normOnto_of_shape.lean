-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.normOnto_of_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:44.838235+00:00
-- url     : https://prove2.me/submissions/c924a2b6-15fc-4da0-9be1-e2805552d8b9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EQMulDiagQMulEQMem
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOntoOfShape
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_isUnit_det_of_witness
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_eQ_mul_diagQ_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero



set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution (hS : NormShape) : NormOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  refine isUnit_det_of_witness h𝔭 ha (by omega) h2 h3 ?_
  intro i j
  rw [← h5, show eQ K 𝔭 k a * W * eQ K 𝔭 k a * diagQ K 𝔭 k a =
      (eQ K 𝔭 k a * W) * (eQ K 𝔭 k a * diagQ K 𝔭 k a) by simp only [Matrix.mul_assoc],
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (eQ_mul_diagQ_mem a l j)
end Formalism.L2.SG.Pf.discriminantNormShapes
