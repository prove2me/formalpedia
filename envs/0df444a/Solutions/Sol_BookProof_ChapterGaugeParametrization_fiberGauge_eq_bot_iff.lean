-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.fiberGauge_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:39.464822+00:00
-- url     : https://prove2.me/submissions/f3e955f7-66df-49f3-bff9-3d23807d7908

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.fiberGauge_eq_bot_iff
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization




open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

variable {X Y : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (π : X → Y) :
    fiberGauge π = ⊥ ↔ Function.Injective π := by

  classical
  constructor
  · intro hbot x y hxy
    by_contra hne
    have hmem : Equiv.swap x y ∈ fiberGauge π := by
      intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hxy]
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hxy]
        · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne ((Equiv.swap_apply_left x y) ▸ congrArg (fun σ : Equiv.Perm X => σ x) hmem).symm
  · intro hinj
    refine le_antisymm (fun σ hσ => ?_) bot_le
    rw [Subgroup.mem_bot]
    ext x
    exact hinj (hσ x)
