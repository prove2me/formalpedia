-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07a_original_BV_C1_random_reserve_semigroup_quotient_L1_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:15:02.991932+00:00
-- url     : https://prove2.me/submissions/52961b0b-5a87-4ff9-9820-e79dfad527ed

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_levy_random_reserve_payoff_L1_stability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (Z : Ω → ℝ)
    (hI : Integrable (fun ω => w (Z ω + X.X t ω)) P)
    (hB : Integrable (fun ω => w (Z ω)) P)
    (hDom : Integrable (fun ω => L * |Z ω - x|) P) :
    |(t : ℝ)⁻¹ *
       ((∫ ω, w (Z ω + X.X t ω) ∂P) - (∫ ω, w (Z ω) ∂P)) -
      (t : ℝ)⁻¹ *
       ((∫ ω, w (x + X.X t ω) ∂P) - w x)| ≤
      2 * (t : ℝ)⁻¹ * (∫ ω, L * |Z ω - x| ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hXInt := avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
    X hX hBV w hwC1 L hL hLip x t ht1
  have hFut := levy_random_reserve_payoff_L1_stability
    X 0 t w L hLip Z (fun _ : Ω => x)
    (by simpa [X.X_zero] using hI)
    (by simpa [X.X_zero] using hXInt) hDom
  have hFut' :
      |(∫ ω, w (Z ω + X.X t ω) ∂P) -
        (∫ ω, w (x + X.X t ω) ∂P)| ≤
          ∫ ω, L * |Z ω - x| ∂P := by
    simpa [X.X_zero] using hFut
  have hBase := levy_random_reserve_payoff_L1_stability
    X 0 0 w L hLip Z (fun _ : Ω => x)
    (by simpa [X.X_zero] using hB)
    (by simpa [X.X_zero] using
      (integrable_const (w x) : Integrable (fun _ : Ω => w x) P)) hDom
  have hBase' :
      |(∫ ω, w (Z ω) ∂P) - w x| ≤
        ∫ ω, L * |Z ω - x| ∂P := by
    simpa [X.X_zero] using hBase
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hInv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htpos.le
  calc
    |(t : ℝ)⁻¹ * ((∫ ω, w (Z ω + X.X t ω) ∂P) -
        (∫ ω, w (Z ω) ∂P)) -
      (t : ℝ)⁻¹ * ((∫ ω, w (x + X.X t ω) ∂P) - w x)|
        = (t : ℝ)⁻¹ *
          |((∫ ω, w (Z ω + X.X t ω) ∂P) -
            (∫ ω, w (x + X.X t ω) ∂P)) -
            ((∫ ω, w (Z ω) ∂P) - w x)| := by
              rw [← mul_sub, abs_mul, abs_of_nonneg hInv]
              congr 1
              ring
    _ ≤ (t : ℝ)⁻¹ *
        (|(∫ ω, w (Z ω + X.X t ω) ∂P) -
          (∫ ω, w (x + X.X t ω) ∂P)| +
         |(∫ ω, w (Z ω) ∂P) - w x|) := by
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hInv
    _ ≤ (t : ℝ)⁻¹ *
        ((∫ ω, L * |Z ω - x| ∂P) +
         (∫ ω, L * |Z ω - x| ∂P)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hFut' hBase') hInv
    _ = 2 * (t : ℝ)⁻¹ * (∫ ω, L * |Z ω - x| ∂P) := by ring
