-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_source_cell_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:07:43.273531+00:00
-- url     : https://prove2.me/submissions/d9b93554-737e-47dd-a798-144e4cd20995

import Mathlib
import Theorems.Thm_avram_chat24_atomic_prefix_interval_core
import Theorems.Thm_AvramDividend_Classical_avram_chat24_discounted_drift_chord_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    (f K : ℝ≥0 → ℝ) (v d a b q : ℝ) (B : ℝ≥0)
    (ha : 0 < a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hf_down : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hK : Monotone K)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B)
    (hs : v + f s - K s ∈ Icc a b) (ht : v + f t - K t ∈ Icc a b)
    (h m : ℝ) (hh : 0 < h) (hgap : (t : ℝ) - (s : ℝ) = h)
    (hmdef : m = d * h - (f t - f s))
    (hsmall : d * h < min (a / 2) 1)
    (w : ℝ → ℝ) (L : ℝ≥0) (hLip : LipschitzOnWith L w (Icc (a / 2) (b + 1))) :
    ‖Real.exp (-(q * (t : ℝ))) *
      ((w (v + f s - K s + d * h - m) - w (v + f s - K s - m)) / h)‖ ≤
        (L : ℝ) * d := by
  have hmass := avram_chat24_atomic_prefix_interval_core f d B hsum hsource s t hst htB
  have he : (∑' r : ℝ≥0,
      if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) = m := by
    rw [hmass.2, hgap, hmdef]
    ring
  have hm : 0 ≤ m := by
    rw [← he]
    apply tsum_nonneg
    intro r
    split_ifs with hr
    · exact sub_nonneg.mpr (hf_down r (lt_of_le_of_lt s.property hr.1))
    · exact le_rfl
  have hbalance : v + f s - K s - m =
      (v + f t - K t) + (K t - K s) - d * h := by
    rw [hmdef]
    ring
  have hlow : a - d * h ≤ v + f s - K s - m := by
    rw [hbalance]
    linarith [ht.1, hK hst]
  exact avram_chat24_discounted_drift_chord_bound
    w L a b (v + f s - K s) m d h q (t : ℝ)
    ha hd hh hq t.property hs hm hlow hsmall hLip
