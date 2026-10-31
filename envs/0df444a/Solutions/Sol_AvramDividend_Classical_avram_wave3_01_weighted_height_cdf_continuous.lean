-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_weighted_height_cdf_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:57:23.943345+00:00
-- url     : https://prove2.me/submissions/3fe60d41-2963-45cc-9e2d-365887dc87da

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology Filter
open scoped ENNReal

/-- A finite weighted distribution of an arbitrary measurable real height is
continuous at any height where its original underlying measure has no atom.
This is the dominated-convergence step for actual killed first-record rewards. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : Ω → ℝ) (w : Ω → ℝ≥0∞)
    (hH : Measurable H) (hw : Measurable w)
    (hfinite : ∫⁻ ω, w ω ∂P ≠ ⊤)
    (a : ℝ) (hAtom : P {ω | H ω = a} = 0) :
    ContinuousAt
      (fun b : ℝ => ∫⁻ ω, if H ω ≤ b then w ω else 0 ∂P) a := by
  have hmeas (b : ℝ) :
      Measurable (fun ω => if H ω ≤ b then w ω else 0) := by
    exact Measurable.ite (measurableSet_le hH measurable_const) hw measurable_const
  have hbound (b : ℝ) :
      ∀ᵐ ω ∂P, (if H ω ≤ b then w ω else 0) ≤ w ω := by
    filter_upwards [] with ω
    split_ifs <;> simp
  have hae : ∀ᵐ ω ∂P, H ω ≠ a := by
    exact ae_iff.mpr (by simpa only [Set.mem_setOf_eq, not_not] using hAtom)
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun b : ℝ => if H ω ≤ b then w ω else 0)
        (nhds a) (nhds (if H ω ≤ a then w ω else 0)) := by
    filter_upwards [hae] with ω hne
    by_cases hlt : H ω < a
    · have heq : (fun b : ℝ => if H ω ≤ b then w ω else 0)
          =ᶠ[nhds a] fun _ => w ω := by
        filter_upwards [eventually_gt_nhds hlt] with b hb
        simp [le_of_lt hb]
      rw [if_pos hlt.le]
      exact tendsto_const_nhds.congr' heq.symm
    · have hgt : a < H ω := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      have heq : (fun b : ℝ => if H ω ≤ b then w ω else 0)
          =ᶠ[nhds a] fun _ => 0 := by
        filter_upwards [eventually_lt_nhds hgt] with b hb
        simp [not_le.mpr hb]
      rw [if_neg (not_le.mpr hgt)]
      exact tendsto_const_nhds.congr' heq.symm
  exact tendsto_lintegral_filter_of_dominated_convergence
    w (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound) hfinite hlim
