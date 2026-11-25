-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G1.det_gram_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:04.991144+00:00
-- url     : https://prove2.me/submissions/743aef4f-4da8-4385-994f-934b6682c9f6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFMapSubtype
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [FiniteDimensional K V]
namespace Formalism.L2.SG.Pf.G1
theorem _root_.solution [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    (hnd : Cnt.NondegOn h X) {n : ℕ} {x : Fin n → V} (hli : LinearIndependent K x)
    (hsp : Submodule.span K (Set.range x) = X) : (U0.gram h x).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hyX : (∑ i, star (c i) • x i) ∈ X := by
    rw [← hsp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ j, h (∑ i, star (c i) • x i) (x j) = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, U0.gram, Matrix.of_apply, Pi.zero_apply] at hj
    simp only [map_sum, map_smulₛₗ, starRingEnd_apply, star_star, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact hj
  have hall : ∀ z ∈ X, h (∑ i, star (c i) • x i) z = 0 := by
    intro z hz
    rw [← hsp] at hz
    have hle : Submodule.span K (Set.range x) ≤ LinearMap.ker (h (∑ i, star (c i) • x i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact key j
    exact hle hz
  have hy0 := hnd _ hyX hall
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i => star (c i)) hy0
  apply hc0
  funext i
  simpa using hcoef i
end Formalism.L2.SG.Pf.G1
