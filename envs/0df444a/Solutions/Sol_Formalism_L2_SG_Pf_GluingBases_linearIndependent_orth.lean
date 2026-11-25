-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.linearIndependent_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:13.982037+00:00
-- url     : https://prove2.me/submissions/63142b42-b6aa-4163-8edd-df90de8e4c75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_InPOfMemPow
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinearIndependentOrth
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg
  rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)
end Formalism.L2.SG.Pf.GluingBases
