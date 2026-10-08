-- Prove2me | solution 1 for BookProof.FockQuadratic.freeOp_commForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:53:45.359389+00:00
-- url     : https://prove2.me/submissions/5f62e1c3-eabe-429d-a52e-85ad431aa60c

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.freeOp_commForm
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) :
    commForm (freeOp hω) (diagMax (sig ω)) x = 0 := by

  rw [commForm_eq_neg_two_im]
  have h := lp.hasSum_inner (𝕜 := ℂ) (freeOp hω x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι))
  have him := Complex.hasSum_im h
  have hzero : ∀ b : Idx ι,
      (inner ℂ (((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b)
        (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ).im = 0 := by
    intro b
    have hb : (inner ℂ (((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b)
        (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ)
        = ((wsum ω b * sig ω b : ℝ) : ℂ) *
          ((starRingEnd ℂ) (((x : L2I (Idx ι)) : Idx ι → ℂ) b)
            * ((x : L2I (Idx ι)) : Idx ι → ℂ) b) := by
      simp only [RCLike.inner_apply, freeOp_coe, diagMax_coe, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    have hcc : (starRingEnd ℂ) (((x : L2I (Idx ι)) : Idx ι → ℂ) b)
        * ((x : L2I (Idx ι)) : Idx ι → ℂ) b
        = ((Complex.normSq (((x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    rw [hb, hcc, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hz : HasSum (fun _ : Idx ι => (0 : ℝ))
      ((inner ℂ (freeOp hω x : L2I (Idx ι)) (diagMax (sig ω) x : L2I (Idx ι)) : ℂ).im) := by
    simpa only [hzero] using him
  rw [hz.unique hasSum_zero]
  ring
