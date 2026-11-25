-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.form_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:06.083917+00:00
-- url     : https://prove2.me/submissions/18c857f0-0cd2-441e-b57a-7f9b90a1460e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesBis
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagQConjTranspose
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_diagQ_conjTranspose
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_conjTranspose
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
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (Y + Z * diagQ K 𝔭 k a)ᴴ * diagQ K 𝔭 k a * (Y + Z * diagQ K 𝔭 k a) - diagQ K 𝔭 k a =
      diagQ K 𝔭 k a * (W + Pᴴ * Z + Zᴴ * P + Zᴴ * diagQ K 𝔭 k a * Z) * diagQ K 𝔭 k a := by
  have hH := diagQ_conjTranspose (K := K) 𝔭 k a
  have h1 : Yᴴ * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Pᴴ := by
    have h := congrArg Matrix.conjTranspose hPY
    rw [conjTranspose_mul, conjTranspose_mul, hH] at h
    exact h.symm
  calc _ = Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a + Yᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a + diagQ K 𝔭 k a * Zᴴ * (diagQ K 𝔭 k a * Y) +
        diagQ K 𝔭 k a * Zᴴ * diagQ K 𝔭 k a * Z * diagQ K 𝔭 k a := by
        simp only [conjTranspose_add, conjTranspose_mul, hH, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_assoc]
        abel
    _ = _ := by
        rw [hW, h1, ← hPY]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
end Formalism.L2.SG.Pf.discriminantNormShapes
