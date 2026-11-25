-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G6.dualF_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:57.040928+00:00
-- url     : https://prove2.me/submissions/b7e40455-6233-4022-bb26-15f723e277d4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GmapEqSelfOfFix
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G6
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G6
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g (dualF h 𝔭 Λ) := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change (∀ y ∈ Formalism.HermitianLatticesTheory.gmap g Λ, h y x ∈ _) ↔ ∀ y ∈ Λ, h y (g.symm x) ∈ _
  constructor
  · intro H y hy
    have := H (g y) (by rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; simpa using hy)
    have e : h (g y) (g (g.symm x)) = h y (g.symm x) := hg y (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rwa [e] at this
  · intro H y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := H _ hy
    have e : h (g (g.symm y)) (g (g.symm x)) = h (g.symm y) (g.symm x) := hg _ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    rwa [e]
end Formalism.L2.SG.Pf.G6
