-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:47:17.1768+00:00
-- url     : https://prove2.me/submissions/1d66d2c0-237f-4285-9a1c-44b1d94dcf4c

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
    (x u : ℝ) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) :
    |(t : ℝ)⁻¹ *
         ((∫ ω, w (u + X.X t ω) ∂P) - w u) -
       (t : ℝ)⁻¹ *
         ((∫ ω, w (x + X.X t ω) ∂P) - w x)| ≤
      2 * L * (t : ℝ)⁻¹ * |u - x| := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have huI : Integrable (fun ω => w (u + X.X t ω)) P :=
    avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
      X hX hBV w hwC1 L hL hLip u t ht1
  have hxI : Integrable (fun ω => w (x + X.X t ω)) P :=
    avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
      X hX hBV w hwC1 L hL hLip x t ht1
  have hDiffI : Integrable
      (fun ω => w (u + X.X t ω) - w (x + X.X t ω)) P :=
    huI.sub hxI
  have hConstI : Integrable (fun _ : Ω => L * |u - x|) P :=
    integrable_const _
  have hBound (ω : Ω) :
      |w (u + X.X t ω) - w (x + X.X t ω)| ≤ L * |u - x| := by
    have hsub : (u + X.X t ω) - (x + X.X t ω) = u - x := by ring
    simpa only [hsub] using hLip (u + X.X t ω) (x + X.X t ω)
  have hExpect :
      |(∫ ω, w (u + X.X t ω) ∂P) -
        (∫ ω, w (x + X.X t ω) ∂P)| ≤ L * |u - x| := by
    rw [← integral_sub huI hxI]
    calc
      |∫ ω, w (u + X.X t ω) - w (x + X.X t ω) ∂P| ≤
          ∫ ω, |w (u + X.X t ω) - w (x + X.X t ω)| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, L * |u - x| ∂P :=
        integral_mono hDiffI.abs hConstI hBound
      _ = L * |u - x| := by simp
  have hTotal :
      |((∫ ω, w (u + X.X t ω) ∂P) -
          (∫ ω, w (x + X.X t ω) ∂P)) -
        (w u - w x)| ≤ 2 * L * |u - x| := by
    calc
      _ ≤ |(∫ ω, w (u + X.X t ω) ∂P) -
              (∫ ω, w (x + X.X t ω) ∂P)| +
              |w u - w x| := abs_sub _ _
      _ ≤ L * |u - x| + L * |u - x| :=
        add_le_add hExpect (hLip u x)
      _ = 2 * L * |u - x| := by ring
  have htInv : 0 ≤ (t : ℝ)⁻¹ := by positivity
  calc
    |(t : ℝ)⁻¹ * ((∫ ω, w (u + X.X t ω) ∂P) - w u) -
       (t : ℝ)⁻¹ * ((∫ ω, w (x + X.X t ω) ∂P) - w x)| =
       |(t : ℝ)⁻¹ *
        (((∫ ω, w (u + X.X t ω) ∂P) -
          (∫ ω, w (x + X.X t ω) ∂P)) -
          (w u - w x))| := by congr 1; ring
    _ = (t : ℝ)⁻¹ *
        |((∫ ω, w (u + X.X t ω) ∂P) -
          (∫ ω, w (x + X.X t ω) ∂P)) -
          (w u - w x)| := by rw [abs_mul, abs_of_nonneg htInv]
    _ ≤ (t : ℝ)⁻¹ * (2 * L * |u - x|) :=
      mul_le_mul_of_nonneg_left hTotal htInv
    _ = 2 * L * (t : ℝ)⁻¹ * |u - x| := by ring
