-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:41:21.681189+00:00
-- url     : https://prove2.me/submissions/75705813-5a28-4c2a-a38f-a3d95dc1dcf4

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution (ρ : G →* Equiv.Perm X) (d : X → ℂ) :
    IsPhysicalFunction ρ d ↔
      ∃ D : observableSpectrum ρ → ℂ, ∀ x : X, d x = D (Quotient.mk (orbitSetoid ρ) x) := by

  constructor
  · intro hd
    refine ⟨Quotient.lift d ?_, fun x => rfl⟩
    rintro x y ⟨g, rfl⟩
    exact (hd g x).symm
  · rintro ⟨D, hD⟩ g x
    rw [hD (ρ g x), hD x]
    exact congrArg D (Quotient.sound ⟨g⁻¹, by rw [map_inv]; simp⟩)
