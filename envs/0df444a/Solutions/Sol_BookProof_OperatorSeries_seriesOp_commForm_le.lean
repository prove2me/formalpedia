-- Prove2me | solution 1 for BookProof.OperatorSeries.seriesOp_commForm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T01:00:18.151251+00:00
-- url     : https://prove2.me/submissions/51fecb62-5bbd-49e1-8a90-f420a2399593

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.seriesOp_commForm_le
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_hasSum
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}

set_option maxHeartbeats 1000000 in
theorem solution
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) {b : κ → ℝ} (hb : Summable b)
    (hcomm : ∀ (k : κ) (x : maxDom c),
      |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x)
    (hq : ∀ x : maxDom c, 0 ≤ quadForm (diagMax c) x) (x : maxDom c) :
    |commForm (seriesOp T a hnorm ha) (diagMax c) x| ≤ (∑' k, b k) * quadForm (diagMax c) x := by

  classical
  set N := diagMax c
  set q : ℝ := quadForm N x with hqdef
  have hq0 : 0 ≤ q := hq x
  -- the inner products sum
  have h1 : HasSum (fun k => (inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ))
      (inner ℂ (seriesOp T a hnorm ha x : L2I ι) (N x : L2I ι)) := by
    have h := (innerSL ℂ (N x : L2I ι)).hasSum (seriesOp_hasSum hnorm ha x)
    have h2 := h.star
    simpa [inner_conj_symm] using h2
  have him : HasSum (fun k => (inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im)
      ((inner ℂ (seriesOp T a hnorm ha x : L2I ι) (N x : L2I ι) : ℂ).im) :=
    (Complex.hasSum_im h1)
  -- each imaginary part is half the commutator form
  have hhalf : ∀ k, |(inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im| ≤ b k * (q / 2) := by
    intro k
    have h := hcomm k x
    rw [commForm_eq_neg_two_im] at h
    rw [abs_mul] at h
    simp only [abs_neg, abs_two] at h
    linarith [h]
  have hsummable : Summable fun k => |(inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im| := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) hhalf ?_
    exact hb.mul_right (q / 2)
  have hbound : |(inner ℂ (seriesOp T a hnorm ha x : L2I ι) (N x : L2I ι) : ℂ).im|
      ≤ ∑' k, b k * (q / 2) := by
    calc |(inner ℂ (seriesOp T a hnorm ha x : L2I ι) (N x : L2I ι) : ℂ).im|
        = |∑' k, (inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im| := by rw [him.tsum_eq]
      _ ≤ ∑' k, |(inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im| := by
          have h := norm_tsum_le_tsum_norm
            (f := fun k => (inner ℂ (T k x : L2I ι) (N x : L2I ι) : ℂ).im)
            (by simpa [Real.norm_eq_abs] using hsummable)
          simpa [Real.norm_eq_abs] using h
      _ ≤ ∑' k, b k * (q / 2) :=
          Summable.tsum_le_tsum hhalf hsummable (hb.mul_right (q / 2))
  have hrw : ∑' k, b k * (q / 2) = (∑' k, b k) * q / 2 := by
    rw [hb.tsum_mul_right]; ring
  rw [commForm_eq_neg_two_im, abs_mul]
  simp only [abs_neg, abs_two]
  rw [hrw] at hbound
  linarith [hbound]
