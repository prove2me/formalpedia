-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.406016+00:00
-- url     : https://prove2.me/submissions/479c39e7-d270-4d5a-95f1-89b3f8e172bc

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_equiv_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type*} [Field K]
variable {V A A' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
  [AddCommGroup A'] [Module K A']
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution [FiniteDimensional K A'] (π : V →ₗ[K] A) (hπ : Function.Surjective π)
    (j j' : A' →ₗ[K] V) (hj : Function.Injective j) (hj' : Function.Injective j')
    (hjj : π ∘ₗ j = π ∘ₗ j') :
    ∃ h : V →ₗ[K] V, Function.Injective h ∧ π ∘ₗ h = π ∧ h ∘ₗ j' = j := by
  obtain ⟨σ, hσ0⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hσ : ∀ x, π (σ x) = x := fun x => by
    simpa using congrArg (fun φ => φ x) hσ0
  set R := π ∘ₗ j' with hR
  set y := kerPart π σ hσ j with hy
  set y' := kerPart π σ hσ j' with hy'
  have hy1 := (injective_iff_kerPart π σ hσ j).mp hj
  have hy1' := (injective_iff_kerPart π σ hσ j').mp hj'
  rw [hjj] at hy1
  have inj : ∀ z : A' →ₗ[K] LinearMap.ker π, LinearMap.ker R ⊓ LinearMap.ker z = ⊥ →
      Function.Injective (z ∘ₗ (LinearMap.ker R).subtype) := by
    intro z hz
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hx2
    apply Subtype.ext
    exact (Submodule.eq_bot_iff _).mp hz x ⟨hx, hx2⟩
  obtain ⟨T, hT⟩ := exists_equiv_comp _ _ (inj y' hy1') (inj y hy1)
  obtain ⟨S, hS⟩ := exists_factor R (y - T.toLinearMap ∘ₗ y') (by
    intro x hx
    have := hT ⟨x, hx⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    simp [this])
  let P : V →ₗ[K] LinearMap.ker π := kerPart π σ hσ LinearMap.id
  have hP : ∀ v, (P v : V) = v - σ (π v) := fun v => rfl
  refine ⟨(LinearMap.ker π).subtype ∘ₗ (T.toLinearMap ∘ₗ P + S ∘ₗ π) + σ ∘ₗ π, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : ((T (P v) + S (π v) : LinearMap.ker π) : V) + σ (π v) = 0 := hv
    have h1 : π v = 0 := by
      have := congrArg π hv'
      simpa [hσ] using this
    rw [h1] at hv'
    simp only [map_zero, add_zero] at hv'
    have h2 : P v = 0 := by
      have : T (P v) = 0 := Subtype.ext hv'
      simpa using this
    have h3 := hP v
    rw [h2, h1] at h3
    simpa using h3.symm
  · ext v; simp [hσ]
  · ext x
    have h1 : P (j' x) = y' x := rfl
    have h2 := hS x
    have h3 : π (j' x) = R x := rfl
    have h4 : π (j x) = R x := by rw [← hjj]; rfl
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.subtype_apply, h1, h3, h2,
      LinearMap.sub_apply, LinearEquiv.coe_coe]
    simp only [add_sub_cancel, hy, kerPart_coe, h4]
    simp
end Formalism.FourierDecayAlt.P.S3x4
