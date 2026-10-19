-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:06:42.25421+00:00
-- url     : https://prove2.me/submissions/4dfd7a57-75dc-4125-9bba-7efbd378e459

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — solution of BookProof.ChapterFreeFieldBornFiberStabilizer.bornFiber_card_mul_signStab_card
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_signStab_card_mul_two_pow_nonzero
import Theorems.Thm_BookProof_ChapterFreeFieldBornFiberStabilizer_posSupport_bornMap
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberStabilizer



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    Nat.card ↥(bornMapSphere n ⁻¹' {bornMapSphere n x}) *
        (signStab (x : EuclideanSpace ℝ (Fin n))).card = 2 ^ n := by

  rw [mul_comm, ← signStab_card_mul_two_pow_nonzero]
  congr 1
  rw [bornFiber_card_general, bornMapSphere_coe, posSupport_bornMap]
