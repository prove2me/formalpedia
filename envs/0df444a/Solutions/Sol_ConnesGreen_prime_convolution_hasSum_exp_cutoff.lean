-- Prove2me | solution 1 for ConnesGreen.prime_convolution_hasSum_exp_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T18:11:59.056978+00:00
-- url     : https://prove2.me/submissions/bf8dfe12-7586-4acb-a87b-079abfa2ef92

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier
open WeilDefect.ConnesNative
open scoped BigOperators
noncomputable section
private theorem boundary_zero (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (x : ℝ) (hx : 2 * t ≤ |x|) :
    conv g (starInv g) x = 0 := by
  unfold conv starInv
  apply integral_eq_zero_of_ae
  filter_upwards [] with s
  by_cases hs : g s = 0
  · simp [hs]
  by_cases hxg : g (-(x - s)) = 0
  · simpa [neg_sub] using (show g s * starRingEnd ℂ (g (-(x - s))) = 0 by rw [hxg]; simp)
  have hs' := hg.2 (subset_tsupport g hs)
  have hxg' := hg.2 (subset_tsupport g hxg)
  have hlt : |x| < 2 * t := abs_lt.mpr ⟨by linarith [hs'.1, hxg'.2],
    by linarith [hs'.2, hxg'.1]⟩
  exact False.elim ((not_lt_of_ge hx) hlt)

theorem solution (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (N : ℕ) (hN : Real.exp (2 * t) < N) :
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n)))
      (∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n))) := by
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n))
  have hz : ∀ n : ℕ, n ∉ Finset.range N → f n = 0 := by
    intro n hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_of_not_gt (by simpa only [Finset.mem_range] using hn) : N ≤ n)
    have hpos : 0 < (n : ℝ) := (Real.exp_pos (2 * t)).trans (hN.trans_le hnN)
    have hlog : 2 * t < Real.log (n : ℝ) :=
      (Real.lt_log_iff_exp_lt hpos).mpr (hN.trans_le hnN)
    have hp := boundary_zero t g hg (Real.log n) (hlog.le.trans (le_abs_self _))
    have hm := boundary_zero t g hg (-Real.log n)
      (by simpa only [abs_neg] using hlog.le.trans (le_abs_self (Real.log (n : ℝ))))
    simp [f, hp, hm]
  have hs : Summable f := by
    apply summable_of_finite_support
    apply (Finset.range N).finite_toSet.subset
    intro n hn
    by_contra h
    exact hn (hz n h)
  have he : (∑' n : ℕ, f n) = ∑ n ∈ Finset.range N, f n := tsum_eq_sum hz
  change HasSum f (∑ n ∈ Finset.range N, f n)
  rw [← he]
  exact hs.hasSum
