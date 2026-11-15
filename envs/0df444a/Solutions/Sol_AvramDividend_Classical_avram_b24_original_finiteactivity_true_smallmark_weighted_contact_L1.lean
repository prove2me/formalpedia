-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_true_smallmark_weighted_contact_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:37:52.717944+00:00
-- url     : https://prove2.me/submissions/2f949b0b-f102-41c1-b4b1-8a42f98f1ad0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (a b : ℕ → Ω → ℝ≥0) (hEndpoints : ∀ k ω, a k ω ≤ T ∧ b k ω ≤ T)
    (W : ℕ → Ω → ℝ) (Wleft : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hWBound : ∀ k ω, ‖W k ω‖ ≤ L) (hWleftBound : ∀ ω, ‖Wleft ω‖ ≤ L)
    (ha : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => a k ω) atTop (𝓝[<] (σ ω)))
    (hb : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => b k ω) atTop (𝓝[Ici (σ ω)] (σ ω)))
    (hW : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω) atTop (𝓝 (Wleft ω)))
    (E : ℕ → Ω → ℝ)
    (hE : ∀ k ω, E k ω =
      if 0 < σ ω then
        W k ω * (Jsmall (b k ω) ω - Jsmall (a k ω) ω) -
        Wleft ω *
          (if -1 < X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) ∧
               X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) < 0
           then X.X (σ ω) ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
           else 0) else 0)
    (hEI : ∀ k, Integrable (E k) P) :
    Tendsto (fun k => ∫ ω, ‖E k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
  let B : Ω → ℝ := fun ω => (N ω).toReal +
    (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
  have hUniform :=
    AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
      X hFinite Jsmall hJsource T
  change Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Jsmall t ω‖ ≤ B ω) at hUniform
  obtain ⟨hBI, hBbound⟩ := hUniform
  have hContact :=
    AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
      X hX hFinite Jsmall hJsource T σ hσ a b W Wleft ha hb hW
  have hMajorI : Integrable (fun ω => 2 * L * B ω + L) P :=
    (hBI.const_mul (2 * L)).add (integrable_const L)
  have hBoundk (k : ℕ) :
      ∀ᵐ ω ∂P, ‖E k ω‖ ≤ 2 * L * B ω + L := by
    filter_upwards [hBbound] with ω hBω
    have hBpos : 0 ≤ B ω := by dsimp [B]; positivity
    by_cases hpos : 0 < σ ω
    · let z : ℝ :=
        X.X (σ ω) ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
      have hScalar :=
        AvramDividend.Classical.avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
          (B ω) L (Jsmall (a k ω) ω) (Jsmall (b k ω) ω) (W k ω)
          (Wleft ω) z hBpos hL (hBω _ (hEndpoints k ω).1)
          (hBω _ (hEndpoints k ω).2) (hWBound k ω) (hWleftBound ω)
      rw [hE k ω, if_pos hpos]
      exact hScalar
    · rw [hE k ω, if_neg hpos, norm_zero]
      have hNonneg : 0 ≤ 2 * L * B ω := mul_nonneg (mul_nonneg (by norm_num) hL) hBpos
      exact add_nonneg hNonneg hL
  have hAE : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hContact] with ω hCω
    by_cases hpos : 0 < σ ω
    · have hEq : (fun k => E k ω) =
          (fun k => W k ω *
            (Jsmall (b k ω) ω - Jsmall (a k ω) ω) -
            Wleft ω *
              (if -1 < X.X (σ ω) ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) ∧
                   X.X (σ ω) ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) < 0
               then X.X (σ ω) ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
               else 0)) := by
        funext k
        simpa only [if_pos hpos] using hE k ω
      rw [hEq]
      convert (hCω hpos).sub tendsto_const_nhds using 1 <;> ring
    · have hEq : (fun k => E k ω) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext k
        simpa only [if_neg hpos] using hE k ω
      rw [hEq]
      exact tendsto_const_nhds
  exact AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
    E (fun ω => 2 * L * B ω + L) hEI hMajorI hBoundk hAE
