-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:38.19659+00:00
-- url     : https://prove2.me/submissions/ccd3fe78-9e8e-40d3-975b-d44d5d2c2068

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Theorems.Thm_BookProof_ChapterGaugeParametrization_apply_eq
import Theorems.Thm_BookProof_ChapterGaugeParametrization_orbit_eq_fiber
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization




open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

variable {X Y : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (π : X → Y) (f : X → ℝ) :
    IsPhysicalObservable (fiberGauge π) f ↔ ∃ F : Y → ℝ, ∀ x, f x = F (π x) := by

  classical
  constructor
  · intro hf
    have hfib : ∀ x y : X, π x = π y → f x = f y := by
      intro x y hxy
      have hmem : y ∈ MulAction.orbit (fiberGauge π) x := by
        rw [orbit_eq_fiber]
        exact hxy.symm
      obtain ⟨σ, hσ⟩ := hmem
      have := hf σ x
      rw [show σ • x = y from hσ] at this
      exact this.symm
    refine ⟨fun y => if h : ∃ x, π x = y then f h.choose else 0, fun x => ?_⟩
    have hex : ∃ z, π z = π x := ⟨x, rfl⟩
    simp only [dif_pos hex]
    exact hfib x hex.choose hex.choose_spec.symm
  · rintro ⟨F, hF⟩ σ x
    rw [hF (σ • x), hF x, apply_eq π σ x]
