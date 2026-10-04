-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.shiftInvert_determines
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:14:59.920674+00:00
-- url     : https://prove2.me/submissions/00cb11fe-06fb-43a4-ab6a-b31ca4b8c775

-- draft 8eaa5e35 from ChapterHashimotoShiftInvert.lean — 
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

set_option autoImplicit false

open BookProof.HashimotoShiftInvert in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h₁ : IsShiftInvert A₁ γ R) (h₂ : IsShiftInvert A₂ γ R) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by
  have key : ∀ {D₁ D₂ : Submodule ℂ F} {B₁ : D₁ →ₗ[ℂ] F} {B₂ : D₂ →ₗ[ℂ] F},
      IsShiftInvert B₁ γ R → IsShiftInvert B₂ γ R → D₁ ≤ D₂ := by
    intro D₁ D₂ B₁ B₂ g₁ g₂ x hx
    obtain ⟨h, -⟩ := g₂.2 (shiftMap B₁ γ ⟨x, hx⟩)
    rwa [g₁.1 ⟨x, hx⟩] at h
  refine ⟨le_antisymm (key h₁ h₂) (key h₂ h₁), ?_⟩
  intro x hx₁ hx₂
  have inj : ∀ u v : F, R u = R v → u = v := by
    intro u v huv
    obtain ⟨hu, hu'⟩ := h₁.2 u
    obtain ⟨hv, hv'⟩ := h₁.2 v
    rw [← hu', ← hv']
    congr 1
    exact Subtype.ext huv
  have e : shiftMap A₁ γ ⟨x, hx₁⟩ = shiftMap A₂ γ ⟨x, hx₂⟩ :=
    inj _ _ (by rw [h₁.1, h₂.1])
  simpa [shiftMap] using e
