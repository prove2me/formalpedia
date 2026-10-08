-- Prove2me | solution 1 for BookProof.FockQuadratic.sig_tgt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:39:43.626802+00:00
-- url     : https://prove2.me/submissions/6b8fc9c7-f61c-4cb9-9d45-74f9c06938ac

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.sig_tgt
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_wsum_add
import Theorems.Thm_BookProof_FockQuadratic_wsum_tsub_of_le
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) :
    sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q := by

  have hd : (deg (tgt P Q a) : ℝ) + deg P = deg a + deg Q := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (deg_tgt (Q := Q) h)
  have hw : wsum ω (tgt P Q a) = wsum ω a - wsum ω P + wsum ω Q := by
    rw [tgt, wsum_add, ← wsum_tsub_of_le (ω := ω) h]
    ring
  simp only [sig, hw]
  linarith
