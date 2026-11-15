-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_dominated_ae_two_noise_cash_excess_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:33:54.576004+00:00
-- url     : https://prove2.me/submissions/f7adcb0c-464e-401e-8a75-e721393d0af4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Ω → ℝ) (w : ℝ) (G J E : ℕ → Ω → ℝ)
    (MG MJ BG BJ : Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ m, Integrable (G m) P)
    (hJI : ∀ m, Integrable (J m) P)
    (hBGI : Integrable BG P) (hBJI : Integrable BJ P)
    (hGB : ∀ m, ∀ᵐ ω ∂P, ‖G m ω‖ ≤ BG ω)
    (hJB : ∀ m, ∀ᵐ ω ∂P, ‖J m ω‖ ≤ BJ ω)
    (hGAE : ∀ᵐ ω ∂P, Tendsto (fun m => G m ω) atTop (𝓝 (MG ω)))
    (hJAE : ∀ᵐ ω ∂P, Tendsto (fun m => J m ω) atTop (𝓝 (MJ ω)))
    (hEAE : ∀ᵐ ω ∂P, Tendsto (fun m => E m ω) atTop (𝓝 (0 : ℝ)))
    (hCash : ∀ m, ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + E m ω) :
    let Epos : ℕ → Ω → ℝ :=
      fun m ω => max (F ω - w - G m ω - J m ω) 0
    (∀ m, Integrable (Epos m) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + Epos m ω) ∧
      Tendsto (fun m => ∫ ω, ‖Epos m ω‖ ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  let Epos : ℕ → Ω → ℝ := fun m ω =>
    max (F ω - w - G m ω - J m ω) 0
  change (∀ m, Integrable (Epos m) P) ∧
    (∀ m, ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + Epos m ω) ∧
    Tendsto (fun m => ∫ ω, ‖Epos m ω‖ ∂P) atTop (𝓝 0)
  have hEI (m : ℕ) : Integrable (Epos m) P := by
    have hGapI : Integrable
        (fun ω => F ω - w - G m ω - J m ω) P :=
      (((hFI.sub (integrable_const w)).sub (hGI m)).sub (hJI m))
    exact hGapI.pos_part
  have hCashE (m : ℕ) :
      ∀ᵐ ω ∂P, F ω ≤ w + G m ω + J m ω + Epos m ω := by
    filter_upwards [] with ω
    have h := le_max_left (F ω - w - G m ω - J m ω) 0
    dsimp [Epos]
    linarith
  let B : Ω → ℝ := fun ω =>
    ‖F ω‖ + ‖w‖ + BG ω + BJ ω
  have hBI : Integrable B P :=
    (((hFI.norm.add (integrable_const ‖w‖)).add hBGI).add hBJI)
  have hDom (m : ℕ) :
      ∀ᵐ ω ∂P, ‖Epos m ω‖ ≤ B ω := by
    filter_upwards [hGB m, hJB m] with ω hgm hjm
    change ‖max (F ω - w - G m ω - J m ω) 0‖ ≤
      ‖F ω‖ + ‖w‖ + BG ω + BJ ω
    exact
      AvramDividend.Classical.avram_b24_original_cash_positive_excess_norm_le_original_two_noise_envelopes
        (F ω) w (G m ω) (J m ω) (BG ω) (BJ ω) hgm hjm
  have hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun m => Epos m ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hGAE, hJAE, hEAE, ae_all_iff.mpr hCash]
      with ω hg hj he hc
    have hRight : Tendsto
        (fun m => w + G m ω + J m ω + E m ω) atTop
        (𝓝 (w + MG ω + MJ ω)) := by
      simpa only [add_zero] using
        (((tendsto_const_nhds.add hg).add hj).add he)
    have hUpper : F ω ≤ w + MG ω + MJ ω :=
      ge_of_tendsto hRight (Eventually.of_forall hc)
    have hNeg : F ω - w - MG ω - MJ ω ≤ 0 := by
      linarith
    have hGlim : Tendsto
        (fun m => max (F ω - w - G m ω - J m ω) 0) atTop
        (𝓝 (max (F ω - w - MG ω - MJ ω) 0)) := by
      exact (((tendsto_const_nhds.sub hg).sub hj).max
        tendsto_const_nhds)
    simpa only [Epos, max_eq_right hNeg] using hGlim
  refine ⟨hEI, hCashE, ?_⟩
  exact
    AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
      Epos B hEI hBI hDom hLimit
