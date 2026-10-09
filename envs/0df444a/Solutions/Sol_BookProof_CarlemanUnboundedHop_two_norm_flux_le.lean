-- Prove2me | solution 1 for BookProof.CarlemanUnboundedHop.two_norm_flux_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:59:25.070317+00:00
-- url     : https://prove2.me/submissions/3c961dbf-00f2-4196-962d-a1162377c003

-- Generated from ChapterCarlemanUnboundedHop.lean — solution of BookProof.CarlemanUnboundedHop.two_norm_flux_le
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Theorems.Thm_BookProof_CarlemanUnboundedHop_theta_le_Theta
import Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_nonneg
import Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_antitone
open BookProof.CarlemanUnboundedHop




open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hu : Summable fun n => ‖u n‖ ^ 2)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hA0 : ∀ n, 0 ≤ A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (N : ℕ) :
    2 * ‖flux a u N‖ ≤ A N * cutMass u Θ N := by

  have hushift : Summable (fun i : ℕ => ‖u (i + (N + 1))‖ ^ 2) :=
    (summable_nat_add_iff (N + 1)).mpr hu
  -- the summability of the tail series, row by row
  have hsθu : ∀ j : ℕ, Summable (fun i : ℕ => θ (i + j + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    intro j
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hθ0 _) (by positivity)) (fun i => ?_)
      (hushift.mul_left (Θ j))
    exact mul_le_mul_of_nonneg_right (theta_le_Theta hθ0 hΘ j i) (by positivity)
  have habs : ∀ n ∈ range (N + 1),
      Summable (fun i : ℕ => ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hmaj : Summable (fun i : ℕ =>
        A N * (θ (i + (N - n) + 1) + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) / 2) := by
      have := (((hΘ (N - n)).summable).add (hsθu (N - n))).mul_left (A N)
      simpa [mul_div_assoc, mul_add] using this.div_const 2
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hmaj
    have hlt : n < i + (N + 1) := by omega
    have hidx : i + (N + 1) - n = i + (N - n) + 1 := by omega
    have hb := hbd n (i + (N + 1)) hlt
    rw [hidx] at hb
    have hAn : A n ≤ A N := hAmono (by omega)
    have hθn : 0 ≤ θ (i + (N - n) + 1) := hθ0 _
    have hun : 0 ≤ ‖u (i + (N + 1))‖ := norm_nonneg _
    have hAN : 0 ≤ A N := hA0 N
    have hb2 : ‖a n (i + (N + 1))‖ ≤ A N * θ (i + (N - n) + 1) :=
      hb.trans (mul_le_mul_of_nonneg_right hAn hθn)
    nlinarith [mul_nonneg (mul_nonneg hAN hθn) (sq_nonneg (‖u (i + (N + 1))‖ - 1)),
      mul_le_mul_of_nonneg_right hb2 hun]
  -- the row estimate
  have key : ∀ n ∈ range (N + 1),
      2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖)
        ≤ A N * (Θ (N - n) * ‖u n‖ ^ 2
            + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    intro n hn
    have hn' : n ≤ N := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
    have habsn := habs n hn
    have hnorm : ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖
        ≤ ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖ := by
      have := norm_tsum_le_tsum_norm (f := fun i : ℕ => a n (i + (N + 1)) * u (i + (N + 1)))
        (by simpa [norm_mul] using habsn)
      simpa [norm_mul] using this
    have hstep1 : 2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖)
        ≤ 2 * (‖u n‖ * ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖) := by
      have := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (u n))
      linarith
    have hmul : 2 * (‖u n‖ * ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖)
        = ∑' i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖)) := by
      rw [← habsn.tsum_mul_left, ← (habsn.mul_left ‖u n‖).tsum_mul_left]
    have hterm : ∀ i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖))
        ≤ A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
      intro i
      have hlt : n < i + (N + 1) := by omega
      have hidx : i + (N + 1) - n = i + (N - n) + 1 := by omega
      have hb := hbd n (i + (N + 1)) hlt
      rw [hidx] at hb
      have hAn : A n ≤ A N := hAmono hn'
      have hθn : 0 ≤ θ (i + (N - n) + 1) := hθ0 _
      have hun : 0 ≤ ‖u (i + (N + 1))‖ := norm_nonneg _
      have hun0 : 0 ≤ ‖u n‖ := norm_nonneg _
      have hAN : 0 ≤ A N := hA0 N
      have hb2 : ‖a n (i + (N + 1))‖ ≤ A N * θ (i + (N - n) + 1) :=
        hb.trans (mul_le_mul_of_nonneg_right hAn hθn)
      nlinarith [mul_nonneg (mul_nonneg hAN hθn) (sq_nonneg (‖u n‖ - ‖u (i + (N + 1))‖)),
        mul_le_mul_of_nonneg_right hb2 (mul_nonneg hun0 hun)]
    have hrhs_sum : Summable (fun i : ℕ => A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
        + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)) :=
      ((((hΘ (N - n)).summable).mul_right (‖u n‖ ^ 2)).add (hsθu (N - n))).mul_left (A N)
    have hstep2 : ∑' i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖))
        ≤ ∑' i : ℕ, A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) :=
      Summable.tsum_mono ((habsn.mul_left ‖u n‖).mul_left 2) hrhs_sum hterm
    have hstep3 : ∑' i : ℕ, A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
        = A N * (Θ (N - n) * ‖u n‖ ^ 2
            + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
      rw [tsum_mul_left, Summable.tsum_add
        (((hΘ (N - n)).summable).mul_right (‖u n‖ ^ 2)) (hsθu (N - n)),
        tsum_mul_right, (hΘ (N - n)).tsum_eq]
    linarith [hstep1, hmul ▸ hstep1, hstep2, hstep3]
  -- assemble
  have hflux1 : ‖flux a u N‖
      ≤ ∑ n ∈ range (N + 1), ‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [norm_mul, RCLike.norm_conj]
  have hflux2 : 2 * ‖flux a u N‖
      ≤ ∑ n ∈ range (N + 1), A N * (Θ (N - n) * ‖u n‖ ^ 2
          + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    have h2 : 2 * ‖flux a u N‖
        ≤ ∑ n ∈ range (N + 1),
            2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖) := by
      rw [← Finset.mul_sum]
      linarith
    exact h2.trans (Finset.sum_le_sum key)
  -- the incoming layer, after interchanging the finite sum with the series
  have hRsum : Summable (fun i : ℕ => Θ i * ‖u (i + (N + 1))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (Theta_nonneg hθ0 hΘ i) (by positivity))
      (fun i => mul_le_mul_of_nonneg_right (Theta_antitone hθ0 hΘ (Nat.zero_le i))
        (by positivity)) (hushift.mul_left (Θ 0))
  have hinter : ∑ n ∈ range (N + 1),
        (∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
      ≤ ∑' i : ℕ, Θ i * ‖u (i + (N + 1))‖ ^ 2 := by
    rw [← Summable.tsum_finsetSum (fun n _ => hsθu (N - n))]
    refine Summable.tsum_mono (summable_sum (fun n _ => hsθu (N - n))) hRsum (fun i => ?_)
    · rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hrefl : ∑ n ∈ range (N + 1), θ (i + (N - n) + 1)
          = ∑ m ∈ range (N + 1), θ (i + m + 1) := by
        simpa using Finset.sum_range_reflect (fun m => θ (i + m + 1)) (N + 1)
      rw [hrefl]
      have hcomm : ∀ m : ℕ, θ (i + m + 1) = θ (m + i + 1) := by
        intro m; rw [Nat.add_comm i m]
      simp_rw [hcomm]
      exact Summable.sum_le_tsum (range (N + 1)) (fun _ _ => hθ0 _) ((hΘ i).summable) |>.trans
        (le_of_eq ((hΘ i).tsum_eq))
  have hfin : ∑ n ∈ range (N + 1), A N * (Θ (N - n) * ‖u n‖ ^ 2
        + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
      ≤ A N * cutMass u Θ N := by
    rw [← Finset.mul_sum, cutMass, Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (by linarith [hinter]) (hA0 N)
  linarith
