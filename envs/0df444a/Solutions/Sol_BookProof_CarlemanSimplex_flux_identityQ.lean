-- Prove2me | solution 1 for BookProof.CarlemanSimplex.flux_identityQ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:11:44.916047+00:00
-- url     : https://prove2.me/submissions/c0f13817-af0b-494e-a3cb-f5860ea1be0a

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.flux_identityQ
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_deg_single
import Theorems.Thm_BookProof_CarlemanSimplex_sum_simplex_hop_im
import Theorems.Thm_BookProof_CarlemanSimplex_sum_mterm_im
import Theorems.Thm_BookProof_CarlemanSimplex_deg_pvec
import Theorems.Thm_BookProof_CarlemanSimplex_lcp_shift
import Theorems.Thm_BookProof_CarlemanSimplex_lcp_vanish
import Theorems.Thm_BookProof_CarlemanSimplex_lc1_vanish_prime
import Theorems.Thm_BookProof_CarlemanTwoStep_lc1_shift
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (hrec : LadderRecQ u lam w W M z) (N : ℕ) :
    z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ sBd d N 1, rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im)
        + ∑ i, ∑ j,
            (∑ a ∈ sBd d N 2, rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im := by

  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
        + (∑ i, ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
        + ∑ i, ∑ j, mterm u M a i j := by
    intro a
    rw [← hrec a, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      · congr 1
        · rw [← hcm (u a)]; ring
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [rtermP, ltermP]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [rtermP, ltermP]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mterm]; ring
  have hL : ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ simplexF d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ simplexF d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, ∑ a ∈ simplexF d N, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
        + (∑ i, ∑ j, ∑ a ∈ simplexF d N, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
        + ∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := by
    calc ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ simplexF d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
            + (∑ i, ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ i, ∑ j, mterm u M a i j) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = ((∑ a ∈ simplexF d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ simplexF d N, ∑ i,
                (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a)
            + ∑ a ∈ simplexF d N, ∑ i, ∑ j,
                (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ a ∈ simplexF d N, ∑ i, ∑ j, mterm u M a i j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ((∑ a ∈ simplexF d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, ∑ a ∈ simplexF d N,
                (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
            + (∑ i, ∑ j, ∑ a ∈ simplexF d N,
                (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := by
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)]
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)
            (f := fun a i => ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))]
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)
            (f := fun a i => ∑ j, mterm u M a i j)]
          have e1 : ∀ i : Fin d, ∑ a ∈ simplexF d N, ∑ j,
              (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a)
              = ∑ j, ∑ a ∈ simplexF d N,
                  (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                    + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a) := fun i =>
            Finset.sum_comm
          have e2 : ∀ i : Fin d, ∑ a ∈ simplexF d N, ∑ j, mterm u M a i j
              = ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := fun i => Finset.sum_comm
          rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun i _ => e2 i]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ simplexF d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq]
  rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add,
    sum_mterm_im hM N, add_zero, Complex.im_sum, Complex.im_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h := sum_simplex_hop_im (u := u) (w := w i) (rc := fun b => rc1 b i)
      (lc := fun b => lc1 b i) (P := Finsupp.single i 1)
      (fun a => lc1_shift i a) (fun a ha => lc1_vanish_prime i a ha) N
    rwa [deg_single] at h
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := sum_simplex_hop_im (u := u) (w := W i j) (rc := fun b => rcp b i j)
      (lc := fun b => lcp b i j) (P := pvec i j)
      (fun a => lcp_shift i j a) (fun a ha => lcp_vanish i j a ha) N
    rwa [deg_pvec] at h
