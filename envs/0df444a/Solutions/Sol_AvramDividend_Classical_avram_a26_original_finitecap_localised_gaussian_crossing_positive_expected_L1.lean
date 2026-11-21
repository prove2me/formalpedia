-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:16:54.944189+00:00
-- url     : https://prove2.me/submissions/e38a208a-7480-45a0-b2c7-8a14b6e30b8f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
open MeasureTheory Set Filter AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y δ : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hδ : ∀ᵐ ω ∂P, Tendsto (fun m => δ m ω) atTop (nhds (0 : ℝ)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ∂P)
      atTop (nhds (0 : ℝ))  := by
  let V : ℝ → ℝ := fun z =>
    if z ≤ c then w z else w c + (z - c)
  let f : ℕ → Ω → ℝ := fun m ω =>
    V (y m ω + δ m ω) - V (y m ω)
  have hAE : ∀ᵐ ω ∂P, Tendsto
      (fun m => max (f m ω) 0) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hy, hδ] with ω hY hD
    have ht := avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
      w c hc hw_cont a b r hr hra hab
      (fun m => y m ω) (fun m => δ m ω) hY hD
    have hMax : Continuous (fun z : ℝ => max z 0) :=
      continuous_id.max continuous_const
    have hlim := hMax.continuousAt.tendsto.comp ht
    simpa [Function.comp_def, f, V] using hlim
  have hDomAll : ∀ᵐ ω ∂P,
      ∀ m, max (f m ω) 0 ≤ B ω := by
    apply (ae_all_iff).2
    intro m
    simpa only [f, V] using hDom m
  have hSummed :=
    avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
      P (fun _ _ => ({0} : Finset ℕ)) (fun m _ ω => f m ω)
      B hBI hB
      (Filter.Eventually.of_forall (fun ω m => by simp))
      (by filter_upwards [hDomAll] with ω hd
          intro m i hi
          exact hd m)
      (by intro m; simpa only [Finset.sum_singleton, f, V] using hMeas m)
      (by filter_upwards [hAE] with ω ht
          simpa only [Finset.sum_singleton] using ht)
  simpa only [Finset.sum_singleton, f, V] using hSummed
