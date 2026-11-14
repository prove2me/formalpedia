-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a199_nonnegative_endpoint_discount_positive_small_large_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:14.874895+00:00
-- url     : https://prove2.me/submissions/db12984c-bfae-4521-b582-c6f6d687eb9a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- A nonnegative raw endpoint value prevents pathological large negative
discount corrections; small cells use local Lipschitz, large cells a compact
start-value bound. This supplies the source exact alternative to a151. -/
theorem solution
    (a Q v u r δ L M : ℝ)
    (ha : 0 ≤ a) (hQa : a ≤ Q)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hu : 0 ≤ u) (hv : v ≤ M)
    (hSmall : |r| < δ → |u - v| ≤ L * |r|) :
    max (-a * (u - v)) 0 ≤
      Q * (if |r| < δ then L * |r| else M) := by
  have hQ : 0 ≤ Q := ha.trans hQa
  by_cases hs : |r| < δ
  · have hh := hSmall hs
    have hneg : -(u - v) ≤ |u - v| := neg_le_abs _
    have hstep : -a * (u - v) ≤ a * |u - v| := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hneg)]
    have hp : 0 ≤ L * |r| := mul_nonneg hL (abs_nonneg _)
    have hmain : -a * (u - v) ≤ Q * (L * |r|) :=
      (hstep.trans (mul_le_mul_of_nonneg_left hh ha)).trans
        (mul_le_mul_of_nonneg_right hQa hp)
    have hzero : 0 ≤ Q * (L * |r|) := mul_nonneg hQ hp
    simpa [hs] using (max_le hmain hzero)
  · have hbounded : -(u - v) ≤ M := by linarith
    have hstep : -a * (u - v) ≤ a * M := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hbounded)]
    have hmain : -a * (u - v) ≤ Q * M :=
      hstep.trans (mul_le_mul_of_nonneg_right hQa hM)
    have hzero : 0 ≤ Q * M := mul_nonneg hQ hM
    simpa [hs] using (max_le hmain hzero)
