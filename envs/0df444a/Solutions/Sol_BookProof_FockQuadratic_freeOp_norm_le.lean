-- Prove2me | solution 1 for BookProof.FockQuadratic.freeOp_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:48:07.810898+00:00
-- url     : https://prove2.me/submissions/c93a56b3-3318-4a48-8d4f-08c9325bfef3

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.freeOp_norm_le
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
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
    ‖(freeOp hω x : L2I (Idx ι))‖ ≤ 1 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by

  have h1 := hasSum_normSq (freeOp hω x : L2I (Idx ι))
  have h2 := hasSum_normSq (diagMax (sig ω) x : L2I (Idx ι))
  have hpt : ∀ b : Idx ι, ‖((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b‖ ^ 2
      ≤ ‖((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b‖ ^ 2 := by
    intro b
    have hb : |wsum ω b| ≤ |sig ω b| := by
      rw [abs_of_nonneg (wsum_nonneg hω b), abs_of_nonneg (sig_nonneg hω b)]
      have h3 : (0 : ℝ) ≤ deg b := Nat.cast_nonneg _
      simp only [sig]; linarith
    have hx : (0 : ℝ) ≤ ‖((x : L2I (Idx ι)) : Idx ι → ℂ) b‖ := norm_nonneg _
    simp only [freeOp_coe, diagMax_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hsq : ‖(freeOp hω x : L2I (Idx ι))‖ ^ 2 ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ ^ 2 := by
    rw [← h1.tsum_eq, ← h2.tsum_eq]
    exact Summable.tsum_le_tsum hpt h1.summable h2.summable
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (freeOp hω x : L2I (Idx ι)),
    norm_nonneg (diagMax (sig ω) x : L2I (Idx ι))]
