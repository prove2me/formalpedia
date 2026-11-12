-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.flux_identity2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:24.812108+00:00
-- url     : https://prove2.me/submissions/f58b1176-4b22-48b7-a696-b707a6edc55c

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.flux_identity2
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_sum_cube_hop_im
import Theorems.Thm_BookProof_CarlemanTwoStep_lc1_shift
import Theorems.Thm_BookProof_CarlemanTwoStep_lc1_vanish
import Theorems.Thm_BookProof_CarlemanTwoStep_lc2_shift
import Theorems.Thm_BookProof_CarlemanTwoStep_lc2_vanish
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hrec : LadderRec2 u lam w1 w2 z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
        + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im := by

  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
        + ∑ i, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
    intro a
    rw [← hrec a, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      · rw [← hcm (u a)]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [rtermG, ltermG]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [rtermG, ltermG]; ring
  have hL : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, ∑ a ∈ cube d N, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
        + ∑ i, ∑ a ∈ cube d N, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
    calc ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ cube d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ i, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a)) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = ((∑ a ∈ cube d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ cube d N, ∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ a ∈ cube d N, ∑ i,
                (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, ∑ a ∈ cube d N, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ i, ∑ a ∈ cube d N,
                (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
          rw [Finset.sum_comm (s := cube d N) (t := Finset.univ),
            Finset.sum_comm (s := cube d N) (t := Finset.univ)]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq]
  rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum,
    Complex.im_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ =>
      sum_cube_hop_im (lc1_shift i) (fun a ha => lc1_vanish i a ha) N
  · exact Finset.sum_congr rfl fun i _ =>
      sum_cube_hop_im (lc2_shift i) (fun a ha => lc2_vanish i a ha) N
