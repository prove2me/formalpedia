-- Prove2me | solution 1 for BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing_prime_iff_injOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:57:55.74799+00:00
-- url     : https://prove2.me/submissions/cd30f3c9-5c19-42b5-b507-d63c257c00d0

-- Generated from ChapterGaugeParametrization.lean — solution of BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing'_iff_injOn
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
theorem solution (π : X → Y) (S : Set X) :
    IsCompleteGaugeFixing' (fiberGauge π) S ↔ Set.InjOn π S := by

  classical
  constructor
  · intro hS x hx y hy hxy
    have hmem : y ∈ MulAction.orbit (fiberGauge π) x := by
      rw [orbit_eq_fiber]
      exact hxy.symm
    obtain ⟨σ, hσ⟩ := hmem
    exact hS x hx y hy σ hσ
  · intro hinj s hs t ht σ hσ
    refine hinj hs ht ?_
    rw [← hσ, apply_eq π σ s]
