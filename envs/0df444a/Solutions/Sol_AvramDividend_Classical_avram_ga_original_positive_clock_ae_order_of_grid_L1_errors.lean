-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_positive_clock_ae_order_of_grid_L1_errors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:21:40.527055+00:00
-- url     : https://prove2.me/submissions/a3edca17-24bf-4b43-8172-dcd3237c057e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f z : Ω → ℝ) (M B R : ℕ → Ω → ℝ)
    (hFZ : Integrable (fun ω => f ω - z ω) μ)
    (hMN : ∀ m, Integrable (fun ω => |z ω - M m ω|) μ)
    (hBN : ∀ m, Integrable (fun ω => |B m ω|) μ)
    (hRN : ∀ m, Integrable (R m) μ)
    (hRpos : ∀ m, ∀ᵐ ω ∂μ, 0 ≤ R m ω)
    (hBudget : ∀ m, ∀ᵐ ω ∂μ,
      f ω ≤ M m ω + B m ω + R m ω)
    (hMlim : Tendsto (fun m => ∫ ω, |z ω - M m ω| ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hBlim : Tendsto (fun m => ∫ ω, |B m ω| ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hRlim : Tendsto (fun m => ∫ ω, R m ω ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂μ, f ω ≤ z ω := by
  classical
  have hPlus : Integrable (fun ω => max (f ω - z ω) 0) μ := by
    simpa [max_comm] using hFZ.pos_part
  have hPoint (m : ℕ) :
      ∀ᵐ ω ∂μ,
        max (f ω - z ω) 0 ≤ |z ω - M m ω| + |B m ω| + R m ω := by
    filter_upwards [hBudget m, hRpos m] with ω hb hr
    have h : f ω - z ω ≤ |z ω - M m ω| + |B m ω| + R m ω := by
      linarith [neg_le_abs (z ω - M m ω), le_abs_self (B m ω)]
    exact max_le h
      (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hr)
  have hBound (m : ℕ) :
      (∫ ω, max (f ω - z ω) 0 ∂μ) ≤
        (∫ ω, |z ω - M m ω| ∂μ) +
        (∫ ω, |B m ω| ∂μ) + (∫ ω, R m ω ∂μ) := by
    have hRI : Integrable (fun ω =>
        |z ω - M m ω| + |B m ω| + R m ω) μ :=
      ((hMN m).add (hBN m)).add (hRN m)
    calc
      _ ≤ (∫ ω, |z ω - M m ω| + |B m ω| + R m ω ∂μ) :=
        integral_mono_ae hPlus hRI (hPoint m)
      _ = (∫ ω, |z ω - M m ω| + |B m ω| ∂μ) +
          (∫ ω, R m ω ∂μ) :=
        integral_add ((hMN m).add (hBN m)) (hRN m)
      _ = _ := congrArg (fun t : ℝ => t + (∫ ω, R m ω ∂μ))
        (integral_add (hMN m) (hBN m))
  have hLim : Tendsto
      (fun m => (∫ ω, |z ω - M m ω| ∂μ) +
        (∫ ω, |B m ω| ∂μ) + (∫ ω, R m ω ∂μ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hMlim.add hBlim).add hRlim
  have hLe : (∫ ω, max (f ω - z ω) 0 ∂μ) ≤ 0 :=
    ge_of_tendsto hLim (Filter.Eventually.of_forall hBound)
  have hNonneg : 0 ≤ (∫ ω, max (f ω - z ω) 0 ∂μ) :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hZero : (∫ ω, max (f ω - z ω) 0 ∂μ) = 0 :=
    le_antisymm hLe hNonneg
  have hAE : (fun ω => max (f ω - z ω) 0) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => le_max_right (f ω - z ω) 0))
      hPlus).mp hZero
  filter_upwards [hAE] with ω hw
  have h : f ω - z ω ≤ 0 :=
    (le_max_left (f ω - z ω) 0).trans (le_of_eq hw)
  exact sub_nonpos.mp h
