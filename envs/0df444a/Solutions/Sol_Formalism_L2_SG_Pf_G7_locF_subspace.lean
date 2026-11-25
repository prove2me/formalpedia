-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G7.locF_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:53.777061+00:00
-- url     : https://prove2.me/submissions/3739acfd-082c-40a2-a2aa-a6e05bb24db8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFSubspace
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_mem
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


section
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.G7
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl
private lemma ne_zero_lemma_4 {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy
end Formalism.L2.SG.Pf.G7
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G7
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.SG.Pf.G7
theorem _root_.solution (U : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) := by
  ext x
  rw [mem_locF_lemma]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := ne_zero_lemma_4 hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact U.smul_mem _ hsx
  · intro hx
    exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
end Formalism.L2.SG.Pf.G7
