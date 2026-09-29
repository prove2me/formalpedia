-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:49:19.86674+00:00
-- url     : https://prove2.me/submissions/9d224f93-38b5-4a7d-a1d4-c48dbea6b983

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_add
import Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_mul
import Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_const
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (cs : List ℝ) (I : CertInterval) (x : ℝ), I.Mem x →
    (evalHorner cs I).Mem (polyEval cs x)
| [], I, x, _ => by
      simpa [evalHorner, polyEval] using mem_const (0 : ℝ)
  | c :: cs, I, x, hx => by
      have hrec := solution cs I x hx
      exact mem_add (mem_mul hrec hx) (mem_const c)
