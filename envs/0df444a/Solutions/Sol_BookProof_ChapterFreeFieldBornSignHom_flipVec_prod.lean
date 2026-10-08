-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignHom.flipVec_prod
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:37:05.308678+00:00
-- url     : https://prove2.me/submissions/11786800-bb66-4ad6-89a7-f8d197728012

-- Generated from ChapterFreeFieldBornSignHom.lean — solution of BookProof.ChapterFreeFieldBornSignHom.flipVec_prod
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignHom



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignAction


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b := by

  norm_num [Finset.prod_ite, flipVec]
  rfl
