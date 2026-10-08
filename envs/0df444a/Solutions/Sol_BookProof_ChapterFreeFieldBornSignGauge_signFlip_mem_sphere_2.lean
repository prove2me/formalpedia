-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:48:30.595142+00:00
-- url     : https://prove2.me/submissions/2895477c-7446-462f-a4cf-1fb3dc68ba28

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge

set_option autoImplicit false

open MeasureTheory
open BookProof.ChapterFreeFieldBorn

open BookProof.ChapterFreeFieldBornSignGauge in
theorem signFlip_norm_aux {n : ℕ} {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖signFlip s x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [signFlip_apply, norm_mul]
  rcases hs k with h | h <;> simp [h]

open BookProof.ChapterFreeFieldBornSignGauge in
theorem solution {n : ℕ} {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    signFlip s x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm] at hx ⊢
  rw [signFlip_norm_aux hs, hx]
