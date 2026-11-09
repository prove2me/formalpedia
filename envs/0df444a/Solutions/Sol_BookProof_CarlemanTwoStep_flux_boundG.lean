-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.flux_boundG
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:51:29.494572+00:00
-- url     : https://prove2.me/submissions/ac3c26f1-2570-4735-bdb5-7ed5ff114756

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.flux_boundG
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
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

theorem solution {w : ℂ} {rc : (Fin d →₀ ℕ) → Fin d → ℝ} (N : ℕ) (i : Fin d) (k : ℕ)
    {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ faceK d N i k, |rc a i| ≤ Cn) :
    |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ faceK d N i k,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2)) := by
  classical
  have h1 : |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ ‖∑ a ∈ faceK d N i k, rtermG u w rc k i a‖ := Complex.abs_im_le_norm _
  have h2 : ‖∑ a ∈ faceK d N i k, rtermG u w rc k i a‖
      ≤ ∑ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖ := norm_sum_le _ _
  have h3 : ∀ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖
      ≤ Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) := by
    intro a ha
    have hnorm : ‖rtermG u w rc k i a‖
        = ‖w‖ * |rc a i| * ‖u a‖ * ‖u (a + Finsupp.single i k)‖ := by
      rw [rtermG]
      simp [Complex.norm_real]
    have hprod : ‖u a‖ * ‖u (a + Finsupp.single i k)‖
        ≤ (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u a‖ - ‖u (a + Finsupp.single i k)‖)]
    have hrcC := hC a ha
    have hb1 : ‖w‖ * |rc a i| ≤ ‖w‖ * Cn := by
      exact mul_le_mul_of_nonneg_left hrcC (norm_nonneg w)
    rw [hnorm]
    calc ‖w‖ * |rc a i| * ‖u a‖ * ‖u (a + Finsupp.single i k)‖
        = (‖w‖ * |rc a i|) * (‖u a‖ * ‖u (a + Finsupp.single i k)‖) := by ring
      _ ≤ (‖w‖ * Cn) * (‖u a‖ * ‖u (a + Finsupp.single i k)‖) := by
          refine mul_le_mul_of_nonneg_right hb1 ?_
          positivity
      _ ≤ (‖w‖ * Cn) * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left hprod ?_
          positivity
      _ = Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) := by ring
  calc |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ ∑ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖ := h1.trans h2
    _ ≤ ∑ a ∈ faceK d N i k,
          Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) :=
        Finset.sum_le_sum h3
    _ = Cn * (‖w‖ * ((∑ a ∈ faceK d N i k,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div]

/-! ## 5. Bessel's inequality with multiplicity -/
