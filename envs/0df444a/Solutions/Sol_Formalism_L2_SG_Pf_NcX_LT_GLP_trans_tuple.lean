-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcX.LT.GLP.trans_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:06.886626+00:00
-- url     : https://prove2.me/submissions/e3870c89-5e14-4c3b-883e-8ba625bff5a0

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  set U := Submodule.span K (Set.range x)
  set U' := Submodule.span K (Set.range y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl U'
  let bx := Module.Basis.span hx
  let by' := Module.Basis.span hy
  have hU : Module.finrank K U = a := by rw [Module.finrank_eq_card_basis bx, Fintype.card_fin]
  have hU' : Module.finrank K U' = a := by rw [Module.finrank_eq_card_basis by', Fintype.card_fin]
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hC'
  let eC : C ≃ₗ[K] C' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let eU : U ≃ₗ[K] U' := bx.equiv by' (Equiv.refl _)
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    ((eU.prodCongr eC).trans (Submodule.prodEquivOfIsCompl _ _ hC')), fun j => ?_⟩
  have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
  simp only [LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC ⟨x j, hxj⟩]
  rw [Submodule.coe_prodEquivOfIsCompl']
  have : eU ⟨x j, hxj⟩ = ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
    have hb : (⟨x j, hxj⟩ : U) = bx j := by ext; simp [bx, Module.Basis.span_apply]
    rw [hb]
    simp only [eU, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact Module.Basis.span_apply hy j
  simp [LinearEquiv.prodCongr_apply, this]
end Formalism.L2.SG.Pf.NcX.LT.GLP
