-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_original_stopped_grid_martingale_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:36:18.772262+00:00
-- url     : https://prove2.me/submissions/a9ff7eb0-3f7c-413c-b09a-ed320c3ead9f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_one_step_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast mFuture : ℕ → MeasurableSpace Ω)
    (hPast : ∀ n, mPast n ≤ mΩ)
    (hFuture : ∀ n, mFuture n ≤ mΩ)
    (hSigma : ∀ n, @SigmaFinite Ω (mPast n) (P.trim (hPast n)))
    (H Z : ℕ → Ω → ℝ)
    (hH : ∀ n, StronglyMeasurable[mPast n] (H n))
    (hZ : ∀ n, StronglyMeasurable[mFuture n] (Z n))
    (hProd : ∀ n, Integrable (H n * Z n) P)
    (hZi : ∀ n, Integrable (Z n) P)
    (hIndep : ∀ n, Indep (mFuture n) (mPast n) P)
    (hCenter : ∀ n, ∫ ω, Z n ω ∂P = 0)
    (hPrefix : ∀ n, StronglyMeasurable[mPast n]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω))
    (hPrefixI : ∀ n, Integrable
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) P)
    (n : ℕ) :
    P[(fun ω => ∑ i ∈ Finset.range (n + 1),
          H i ω * Z i ω) | mPast n] =ᵐ[P]
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by
  letI : @SigmaFinite Ω (mPast n) (P.trim (hPast n)) := hSigma n
  have hstep :=
    AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_one_step_martingale
      P (mPast n) (mFuture n) (hPast n) (hFuture n)
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω)
      (H n) (Z n)
      (hPrefix n) (hPrefixI n) (hH n) (hZ n)
      (hProd n) (hZi n) (hIndep n) (hCenter n)
  have hfun :
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) + (H n * Z n) =
        (fun ω => ∑ i ∈ Finset.range (n + 1), H i ω * Z i ω) := by
    funext ω
    simp [Finset.sum_range_succ]
  rw [hfun] at hstep
  exact hstep
