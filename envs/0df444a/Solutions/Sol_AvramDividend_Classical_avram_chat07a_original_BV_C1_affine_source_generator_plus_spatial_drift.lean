-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07a_original_BV_C1_affine_source_generator_plus_spatial_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:56:25.947596+00:00
-- url     : https://prove2.me/submissions/66ee53dc-1786-445d-a22c-031924d811a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- First-order deterministic reserve motion adds its spatial derivative
    to the actual BV Lévy transition generator on the original sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (d : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, w (x + X.X (Real.toNNReal h) ω + d * h) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.generator w x + d * deriv w x)) := by
  let B : ℝ → ℝ := fun h => h⁻¹ *
    ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x)
  let S : ℝ → ℝ := fun h =>
    ∫ ω, h⁻¹ * (w (x + X.X (Real.toNNReal h) ω + d * h) -
                    w (x + X.X (Real.toNNReal h) ω)) ∂P
  have hFixed : Tendsto B (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.generator w x)) := by
    simpa [B] using
      (bv_levy_transition_right_generator_of_global_C1_lipschitz
        X hX hBV w hwC1 L hL hLip x hgen)
  have hDriftNeg :=
    avram_wave5_04c_original_C1_source_drift_expectation_right_slope
      X w hwC1 L hL hLip x (-d)
  have hDrift : Tendsto S (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (d * deriv w x)) := by
    convert hDriftNeg.neg using 1
    · funext h
      dsimp [S]
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with ω
      have heq : x + X.X (Real.toNNReal h) ω - (-d) * h =
          x + X.X (Real.toNNReal h) ω + d * h := by ring
      rw [heq]
      ring
    · ring
  have hNear : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < h ∧ h < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds] with h hpos hlt
    exact ⟨hpos, hlt⟩
  have hCombined : Tendsto (fun h => B h + S h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.generator w x + d * deriv w x)) :=
    hFixed.add hDrift
  apply hCombined.congr'
  filter_upwards [hNear] with h hh
  obtain ⟨hh0, hh1⟩ := hh
  have ht : Real.toNNReal h ≤ (1 : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    simpa [Real.coe_toNNReal, max_eq_left hh0.le] using le_of_lt hh1
  have hIbase : Integrable
      (fun ω => w (x + X.X (Real.toNNReal h) ω)) P :=
    avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
      X hX hBV w hwC1 L hL hLip x (Real.toNNReal h) ht
  have hIshift : Integrable
      (fun ω => w (x + X.X (Real.toNNReal h) ω + d * h)) P := by
    have hRaw :=
      avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
        X hX hBV w hwC1 L hL hLip (x + d * h)
        (Real.toNNReal h) ht
    convert hRaw using 1
    funext ω
    congr 1
    ring
  have hSub :
      (∫ ω, w (x + X.X (Real.toNNReal h) ω + d * h) -
                 w (x + X.X (Real.toNNReal h) ω) ∂P) =
      (∫ ω, w (x + X.X (Real.toNNReal h) ω + d * h) ∂P) -
      (∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) :=
    integral_sub hIshift hIbase
  change B h + S h = h⁻¹ *
    ((∫ ω, w (x + X.X (Real.toNNReal h) ω + d * h) ∂P) - w x)
  dsimp [B, S]
  rw [integral_const_mul, hSub]
  ring
