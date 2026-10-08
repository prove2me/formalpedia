-- Prove2me | solution 1 for BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:44:57.846075+00:00
-- url     : https://prove2.me/submissions/3835cae3-ce61-4807-937e-e032dd4ebdc5

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.abs_sig_sub_sig_tgt_le
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_FockQuadratic_sig_tgt
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) {P Q b : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (h : P ≤ b) : |sig ω b - sig ω (tgt P Q b)| ≤ wsum ω P + wsum ω Q + 2 := by

  have hst := sig_tgt (ω := ω) (P := P) (Q := Q) h
  have h1 : (0 : ℝ) ≤ wsum ω P := wsum_nonneg hω _
  have h2 : (0 : ℝ) ≤ wsum ω Q := wsum_nonneg hω _
  have h3 : (deg P : ℝ) + (deg Q : ℝ) ≤ 2 := by
    exact_mod_cast (by exact_mod_cast hPQ : deg P + deg Q ≤ 2)
  have h4 : (0 : ℝ) ≤ (deg P : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ (deg Q : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> [linarith; linarith]
