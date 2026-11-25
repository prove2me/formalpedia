-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.eq_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:36:14.012209+00:00
-- url     : https://prove2.me/submissions/88c60abe-9f1a-4767-8346-dda78e267f00

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_diagQ_conjTranspose
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
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : Fin m → 𝓞 F}
    (P W Z Z' : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    W + Pᴴ * (Z + Z') + (Z + Z')ᴴ * P + (Z + Z')ᴴ * diagQ K 𝔭 k a * (Z + Z') =
      (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) + (P + diagQ K 𝔭 k a * Z)ᴴ * Z' +
        Z'ᴴ * (P + diagQ K 𝔭 k a * Z) + Z'ᴴ * diagQ K 𝔭 k a * Z' := by
  simp only [conjTranspose_add, conjTranspose_mul, diagQ_conjTranspose, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]
  abel
end Formalism.L2.SG.Pf.discriminantNormShapes
