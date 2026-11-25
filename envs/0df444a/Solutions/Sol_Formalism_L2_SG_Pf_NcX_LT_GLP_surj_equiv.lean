-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcX.LT.GLP.surj_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:05.174993+00:00
-- url     : https://prove2.me/submissions/d1a5ce88-01a6-4c02-9289-7be8b63f64d8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcXGLP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcX Formalism.L2.SG.Pf.NcX.LT Formalism.L2.SG.Pf.NcX.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcX.LT.GLP
theorem _root_.solution {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨D1, hD1⟩ := Submodule.exists_isCompl (LinearMap.ker L1)
  obtain ⟨D2, hD2⟩ := Submodule.exists_isCompl (LinearMap.ker L2)
  let e1 : D1 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD1).symm.trans (L1.quotKerEquivOfSurjective h1)
  let e2 : D2 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD2).symm.trans (L2.quotKerEquivOfSurjective h2)
  have he1 : ∀ d : D1, e1 d = L1 d := fun d => by
    simp [e1, Submodule.quotientEquivOfIsCompl_symm_apply]
  have he2 : ∀ d : D2, e2 d = L2 d := fun d => by
    simp [e2, Submodule.quotientEquivOfIsCompl_symm_apply]
  have : FiniteDimensional K W := Module.Finite.of_surjective L1 h1
  have hk : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have a1 := LinearMap.finrank_range_add_finrank_ker L1
    have a2 := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.2 h1, finrank_top] at a1
    rw [LinearMap.range_eq_top.2 h2, finrank_top] at a2
    omega
  let k : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := LinearEquiv.ofFinrankEq _ _ hk
  let δ : C ≃ₗ[K] C := (Submodule.prodEquivOfIsCompl _ _ hD2).symm.trans
    ((k.prodCongr (e2.trans e1.symm)).trans (Submodule.prodEquivOfIsCompl _ _ hD1))
  refine ⟨δ, fun c => ?_⟩
  set p := (Submodule.prodEquivOfIsCompl _ _ hD2).symm c with hp
  have hc : c = (p.1 : C) + (p.2 : C) := by
    rw [← Submodule.coe_prodEquivOfIsCompl' _ _ hD2, hp, LinearEquiv.apply_symm_apply]
  have hδ : δ c = ((k p.1 : LinearMap.ker L1) : C) + ((e1.symm (e2 p.2) : D1) : C) := by
    simp only [δ, LinearEquiv.trans_apply, ← hp]
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [hδ, map_add, LinearMap.mem_ker.1 (k p.1).2, zero_add, ← he1, LinearEquiv.apply_symm_apply, he2]
  conv_rhs => rw [hc]
  rw [map_add, LinearMap.mem_ker.1 p.1.2, zero_add]
end Formalism.L2.SG.Pf.NcX.LT.GLP
