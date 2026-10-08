-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignGauge.signFlip_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:41:06.343987+00:00
-- url     : https://prove2.me/submissions/2d5ff75c-381e-4adf-83ba-5e26e92de57f

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge

set_option autoImplicit false

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge in
theorem solution {n : ℕ} {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖signFlip s x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [signFlip_apply, norm_mul]
  rcases hs k with h | h <;> simp [h]
