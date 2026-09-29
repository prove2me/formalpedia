-- Prove2me | solution 1 for GaloisRepAdic.isStrictOrdinaryAt_of_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/61a643af-1fe8-5c8c-a373-7ef3e478c2d7

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv

set_option autoImplicit false

namespace P2mStrictEquiv

variable {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A}

theorem map_apply_symm (e : GaloisRepAdic.Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ρ₂.V) :
    ρ₂.ρ σ y = e.toLinearEquiv (ρ₁.ρ σ (e.toLinearEquiv.symm y)) := by
  rw [e.map_apply, LinearEquiv.apply_symm_apply]

theorem map_span_singleton (e : GaloisRepAdic.Equiv ρ₁ ρ₂) (w : ρ₁.V) :
    (A ∙ w).map (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) = A ∙ e.toLinearEquiv w := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl

end P2mStrictEquiv

open P2mStrictEquiv in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsStrictOrdinaryAt p) : ρ₂.IsStrictOrdinaryAt p := by
  obtain ⟨e⟩ := e
  obtain ⟨hpA, h⟩ := h
  refine ⟨hpA, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, rfl⟩, hD, hI, hS⟩ := h P hP
  set E : ρ₁.V ≃ₗ[A] ρ₂.V := e.toLinearEquiv with hE
  have hmem : ∀ {v : ρ₁.V}, v ∈ A ∙ b 0 → E v ∈ A ∙ E (b 0) := by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨A ∙ E (b 0), ⟨b.map E, by rw [Module.Basis.map_apply]⟩, ?_, ?_, ?_⟩
  ·
    intro σ hσ v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, map_apply_symm e, ← hE, LinearEquiv.symm_apply_apply]
    exact Submodule.smul_mem _ _ (hmem (hD σ hσ _ (Submodule.mem_span_singleton_self _)))
  ·
    intro σ hσ v
    have h1 : ρ₂.ρ σ v - v = E (ρ₁.ρ σ (E.symm v) - E.symm v) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
    rw [h1]
    exact hmem (hI σ hσ _)
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hc⟩ := hS σ hσ
    refine ⟨x, z, ?_, ?_, hc⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_apply_symm e, ← hE, map_smul, LinearEquiv.symm_apply_apply,
        ← map_smul E, hx _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
        map_smul, map_smul, smul_comm]
    · intro v
      have h1 : ρ₂.ρ σ v - z • v = E (ρ₁.ρ σ (E.symm v) - z • E.symm v) := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
      rw [h1]
      exact hmem (hz _)

end S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv
end P2MW
export P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv (solution)
