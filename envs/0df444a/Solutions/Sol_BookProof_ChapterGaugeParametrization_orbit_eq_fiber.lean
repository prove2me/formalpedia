-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.orbit_eq_fiber
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:36.931874+00:00
-- url     : https://prove2.me/submissions/a661e51b-ac9a-4d03-baaa-66572a0aaac3

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.orbit_eq_fiber
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Theorems.Thm_BookProof_ChapterGaugeParametrization_apply_eq
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization




open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

variable {X Y : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (π : X → Y) (x : X) :
    MulAction.orbit (fiberGauge π) x = π ⁻¹' {π x} := by

  classical
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    exact apply_eq π σ x
  · intro hy
    have hy' : π y = π x := hy
    refine ⟨⟨Equiv.swap x y, ?_⟩, ?_⟩
    · intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hy']
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hy']
        · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    · change Equiv.swap x y x = y
      simp
