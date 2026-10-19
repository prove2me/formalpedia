-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:40:04.549858+00:00
-- url     : https://prove2.me/submissions/c1b69ed7-ee56-4990-979f-54be759e0240

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_permOp_isFunctionOfSpectrum_iff
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution [Nonempty X]
    {ρ : G →* Equiv.Perm X} (hmoves : ∀ g : G, g ≠ 1 → ∀ x : X, ρ g x ≠ x) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by

  intro g hg hmem
  have hρg : ρ g = 1 := (permOp_isFunctionOfSpectrum_iff (ρ g)).1 hmem
  obtain ⟨x⟩ := ‹Nonempty X›
  exact hmoves g hg x (by rw [hρg]; rfl)
