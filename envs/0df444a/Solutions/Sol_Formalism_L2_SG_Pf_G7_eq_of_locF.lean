-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G7.eq_of_locF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:00:19.867238+00:00
-- url     : https://prove2.me/submissions/63573a31-7bb8-4dc3-9626-80961f314c13

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
private lemma mem_image_lemma_5 {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, fun hab => (hp.mem_or_mem hab).elim ha hb, map_mul _ _ _⟩
private lemma le_of_locF_lemma_6 (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A ≤ B := by
  intro x hx
  let J : Ideal (𝓞 F) :=
    Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (B.comap (LinearMap.toSpanSingleton (𝓞 K) V x))
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal J hne
    have hxA : x ∈ locF 𝔭 A :=
      (mem_locF_lemma 𝔭 A x).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [hAB 𝔭 hmax] at hxA
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 B x).mp hxA
    obtain ⟨t, ht, rfl⟩ := mem_image_lemma_5 hmax.isPrime hs
    exact ht (hle (show t ∈ J from hsx))
  have h1 : (1 : 𝓞 F) ∈ J := by rw [hJ]; exact Submodule.mem_top
  simpa [J] using h1
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
theorem _root_.solution (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A = B := le_antisymm (le_of_locF_lemma_6 A B hAB) (le_of_locF_lemma_6 B A fun 𝔭 h => (hAB 𝔭 h).symm)
end Formalism.L2.SG.Pf.G7
