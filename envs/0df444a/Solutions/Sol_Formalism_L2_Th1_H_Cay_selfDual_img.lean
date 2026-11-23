-- Prove2me | solution 1 for Formalism.L2.Th1.H.Cay.selfDual_img
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:48.072985+00:00
-- url     : https://prove2.me/submissions/8c0efcaf-508c-400e-a449-a7eb3bccc98f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.Cay
namespace Formalism.L2.Th1.H.Cay
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (δ : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hΛ : IsSelfDual H Λ) :
    IsSelfDual H (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hδ a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H x y = m := hx
    rw [imgLat, AddSubgroup.mem_map]
    refine ⟨δ.symm x, ?_, by simp⟩
    rw [← hΛ]
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H (δ.symm x) y = m
    intro y hy
    obtain ⟨m, hm⟩ := hx' (δ y) (by rw [imgLat, AddSubgroup.mem_map]; exact ⟨y, hy, rfl⟩)
    refine ⟨m, ?_⟩
    have e := hi (δ.symm x) y
    rw [LinearEquiv.apply_symm_apply] at e
    show (H (δ.symm x) y).im = m
    rw [← e]; exact hm
  · intro hx
    rw [imgLat, AddSubgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← hΛ] at ha
    have ha' : ∀ y ∈ Λ, ∃ m : ℤ, altE H a y = m := ha
    show ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H (δ a) y = m
    intro y hy
    rw [imgLat, AddSubgroup.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨m, hm⟩ := ha' b hb
    refine ⟨m, ?_⟩
    show (H (δ a) (δ b)).im = m
    rw [hi]; exact hm
end Formalism.L2.Th1.H.Cay
