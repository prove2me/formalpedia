-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.lift_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:16.56409+00:00
-- url     : https://prove2.me/submissions/e7bd6722-f8ac-4724-acbd-b6afa300a3e2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {R P P' V : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] [AddCommGroup V] [Module R V]
    (L S0 : Submodule R P) (L' S0' : Submodule R P') (Λ : P →ₗ[R] V) (Λ' : P' →ₗ[R] V)
    (DD : V →ₗ[R] V) (φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L'))
    (hS : S0 ≤ L) (hS' : S0' ≤ L') (hk : ∀ x ∈ S0, Λ x = 0) (hk' : ∀ y ∈ S0', Λ' y = 0)
    (h1 : ∀ x ∈ L, DD (Λ x) = 0 → x ∈ S0) (h1' : ∀ y ∈ L', Λ' y = 0 → y ∈ S0')
    (h2 : ∀ x, ∃ y, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x))
    (h3 : ∀ y, ∃ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) :
    ∃ Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0'), ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) := by
  let f : P →ₗ[R] (P' ⧸ L') × V := LinearMap.prod (φ.toLinearMap.comp L.mkQ) (DD.comp Λ)
  let f' : P' →ₗ[R] (P' ⧸ L') × V := LinearMap.prod L'.mkQ Λ'
  have fx : ∀ x, f x = (φ (Submodule.Quotient.mk x), DD (Λ x)) := fun x => rfl
  have fy : ∀ y, f' y = (Submodule.Quotient.mk y, Λ' y) := fun y => rfl
  have hf : S0 ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker, fx, (Submodule.Quotient.mk_eq_zero L).2 (hS hx), map_zero, hk x hx,
      map_zero]
    rfl
  have hf' : S0' ≤ LinearMap.ker f' := by
    intro y hy
    rw [LinearMap.mem_ker, fy, (Submodule.Quotient.mk_eq_zero L').2 (hS' hy), hk' y hy]
    rfl
  have kf : LinearMap.ker f ≤ S0 := by
    intro x hx
    rw [LinearMap.mem_ker, fx, Prod.mk_eq_zero] at hx
    have hxL : x ∈ L := by
      rw [← Submodule.Quotient.mk_eq_zero L]
      exact φ.map_eq_zero_iff.1 hx.1
    exact h1 x hxL hx.2
  have kf' : LinearMap.ker f' ≤ S0' := by
    intro y hy
    rw [LinearMap.mem_ker, fy, Prod.mk_eq_zero] at hy
    exact h1' y ((Submodule.Quotient.mk_eq_zero L').1 hy.1) hy.2
  let ι := S0.liftQ f hf
  let ι' := S0'.liftQ f' hf'
  have hι : Function.Injective ι := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ kf)
  have hι' : Function.Injective ι' :=
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ kf')
  have hr : LinearMap.range ι = LinearMap.range ι' := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := h2 x
      exact ⟨y, by rw [fx, fy, hy1, hy2]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := h3 y
      exact ⟨x, by rw [fx, fy, hx1, hx2]⟩
  let Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0') :=
    (LinearEquiv.ofInjective ι hι).trans
      ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective ι' hι').symm)
  have key : ∀ z, ι' (Ψ z) = ι z := by
    intro z
    have h := (LinearEquiv.ofInjective ι' hι').apply_symm_apply
      (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective ι hι z))
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨Ψ, fun x y => ?_⟩
  have e1 : ι (Submodule.Quotient.mk x) = f x := rfl
  have e2 : ι' (Submodule.Quotient.mk y) = f' y := rfl
  rw [← hι'.eq_iff, key, e1, e2, fx, fy, Prod.mk.injEq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
end Formalism.FourierDecayAlt.P.A5x9
