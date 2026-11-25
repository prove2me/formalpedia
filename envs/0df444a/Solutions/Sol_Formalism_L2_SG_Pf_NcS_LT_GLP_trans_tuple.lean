-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcS.LT.GLP.trans_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:29.686681+00:00
-- url     : https://prove2.me/submissions/a08d0310-53d1-4d5b-8d9f-77da9162388b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NcSGLP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcS Formalism.L2.SG.Pf.NcS.LT Formalism.L2.SG.Pf.NcS.LT.GLP
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.NcS.LT.GLP
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  obtain ⟨CX, hX⟩ := Submodule.exists_isCompl (Submodule.span K (Set.range x))
  obtain ⟨CY, hY⟩ := Submodule.exists_isCompl (Submodule.span K (Set.range y))
  have hdim : Module.finrank K CX = Module.finrank K CY := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hX
    have h2 := Submodule.finrank_add_eq_of_isCompl hY
    rw [finrank_span_eq_card hx] at h1
    rw [finrank_span_eq_card hy] at h2
    omega
  let bx := Module.Basis.span hx
  let bY := Module.Basis.span hy
  let e1 := bx.equiv bY (Equiv.refl (Fin a))
  let e2 : CX ≃ₗ[K] CY := by
    first
    | exact LinearEquiv.ofFinrankEq _ _ hdim
    | exact LinearEquiv.ofFinrankEq hdim
  let P : (Submodule.span K (Set.range x) × CX) ≃ₗ[K] (Submodule.span K (Set.range y) × CY) := by
    first
    | exact LinearEquiv.prodCongr e1 e2
    | exact LinearEquiv.prod e1 e2
  have hsymm : ∀ j, (Submodule.prodEquivOfIsCompl _ _ hX).symm (x j) = (bx j, 0) := by
    intro j
    rw [LinearEquiv.symm_apply_eq]
    first
    | (rw [Submodule.coe_prodEquivOfIsCompl']; simp [bx, Module.Basis.span_apply])
    | simp [bx, Module.Basis.span_apply]
    | simp [bx]
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hX).symm.trans (P.trans (Submodule.prodEquivOfIsCompl _ _ hY)),
    fun j => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hsymm j]
  have hP : P (bx j, 0) = (bY j, 0) := by
    first
    | (show (e1 (bx j), e2 0) = (bY j, 0)
       rw [map_zero]
       simp [e1, Module.Basis.equiv_apply])
    | simp [P, e1, Module.Basis.equiv_apply]
    | simp [P, e1]
  rw [hP]
  first
  | (rw [Submodule.coe_prodEquivOfIsCompl']; simp [bY, Module.Basis.span_apply])
  | simp [bY, Module.Basis.span_apply]
  | simp [bY]
end Formalism.L2.SG.Pf.NcS.LT.GLP
