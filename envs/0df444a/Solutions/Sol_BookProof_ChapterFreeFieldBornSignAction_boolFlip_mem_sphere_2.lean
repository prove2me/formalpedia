-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:54:17.299498+00:00
-- url     : https://prove2.me/submissions/f497abc9-b45c-4ec1-9c46-14187ace0512

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignAction

set_option autoImplicit false

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

open BookProof.ChapterFreeFieldBornSignGauge in
theorem signFlip_norm_aux {n : ℕ} {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖signFlip s x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [signFlip_apply, norm_mul]
  rcases hs k with h | h <;> simp [h]

open BookProof.ChapterFreeFieldBornSignAction in
theorem flipVec_pm_aux {n : ℕ} (b : Fin n → Bool) (k : Fin n) :
    flipVec b k = 1 ∨ flipVec b k = -1 := by
  unfold flipVec
  cases b k <;> simp

open BookProof.ChapterFreeFieldBornSignAction in
theorem solution {n : ℕ} (b : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    boolFlip b x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm] at hx ⊢
  unfold boolFlip
  rw [signFlip_norm_aux (flipVec_pm_aux b), hx]
