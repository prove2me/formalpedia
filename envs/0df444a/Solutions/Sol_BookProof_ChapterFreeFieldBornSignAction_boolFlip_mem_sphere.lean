-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:16:47.28113+00:00
-- url     : https://prove2.me/submissions/7905c17e-be5c-441a-ba26-3db84553ece4

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_flipVec_pm
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_mem_sphere
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    boolFlip b x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := signFlip_mem_sphere (flipVec_pm b) hx
