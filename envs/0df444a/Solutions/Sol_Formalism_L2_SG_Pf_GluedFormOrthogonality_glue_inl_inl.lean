-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluedFormOrthogonality.glue_inl_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:16:47.684453+00:00
-- url     : https://prove2.me/submissions/bf53796f-9048-48ac-b6b4-bfc7aa71f4cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueInlInl
import Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_form_U_orth
import Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_form_orth_U
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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1 h2 h2
  · exact hbo _ _ hii
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _)]
  · simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_orth_U hs (hbU i') (hwW _)]
  · have hτ' : τ i ≠ τ i' := fun e => hii (hτ i i' h1 h2 e)
    simp only [map_smulₛₗ, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _),
      form_orth_U hs (hbU i') (hwW _), hwo _ _ hτ']
end Formalism.L2.SG.Pf.GluedFormOrthogonality
