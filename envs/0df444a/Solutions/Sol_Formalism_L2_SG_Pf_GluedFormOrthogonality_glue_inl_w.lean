-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluedFormOrthogonality.glue_inl_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:31.5394+00:00
-- url     : https://prove2.me/submissions/b0cc0da9-b7a7-4446-9535-e11d1b28a069

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueInlInl
import Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_form_U_orth
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
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluedFormOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.GluedFormOrthogonality
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hwW : ∀ j, w j ∈ orthK h U)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) {i : Fin n} {j : Fin m}
    (hj : vF 𝔭 (a i) ≠ 0 → τ i ≠ j) :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (w j) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1
  · exact form_U_orth (hbU i) (hwW j)
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, form_U_orth (hbU i) (hwW j), hwo _ _ (hj h1)]
end Formalism.L2.SG.Pf.GluedFormOrthogonality
