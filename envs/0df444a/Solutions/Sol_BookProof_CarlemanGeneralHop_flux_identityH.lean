-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.flux_identityH
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T06:53:36.607772+00:00
-- url     : https://prove2.me/submissions/ce33b8bd-a9eb-423d-a115-9fc70b8c30e2

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.flux_identityH
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_sum_hop_im
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {ι : Type*} [Fintype ι] {lam : (Fin d →₀ ℕ) → ℝ} {p m : ι → (Fin d →₀ ℕ)}
  {c c' : ι → (Fin d →₀ ℕ) → ℝ} {w : ι → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution
    (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) →
      c' h (hshift (p h) (m h) b) = c h b)
    (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0)
    (hrec : LadderRecH u lam p m c c' w z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = ∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
            rtG u (w h) (c h) (p h) (m h) a).im
          - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
            rtG u (w h) (c h) (p h) (m h) b).im) := by

  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
            + ltG u (w h) (c' h) (p h) (m h) a) := by
    intro a
    rw [← hrec a, mul_add, Finset.mul_sum]
    congr 1
    · rw [← hcm (u a)]; ring
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [rtG, ltG]; ring
  have hL : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + ∑ h : ι, ∑ a ∈ cube d N, (rtG u (w h) (c h) (p h) (m h) a
            + ltG u (w h) (c' h) (p h) (m h) a) := by
    calc ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ cube d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a)) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = (∑ a ∈ cube d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ cube d N, ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a) := Finset.sum_add_distrib
      _ = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + ∑ h : ι, ∑ a ∈ cube d N, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a) := by
          rw [Finset.sum_comm (s := cube d N) (t := Finset.univ)]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum]
  exact Finset.sum_congr rfl fun h _ => sum_hop_im (hcomp h) (hvanL h) (cube d N)
