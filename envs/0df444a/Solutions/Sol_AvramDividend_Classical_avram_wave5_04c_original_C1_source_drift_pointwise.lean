-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:36:38.157441+00:00
-- url     : https://prove2.me/submissions/cd098481-94a1-4603-b28c-89d7eabe2ddc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_drift_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Pointwise first-order drift shifts along the actual Lévy source path. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (x d : ℝ) (ω : Ω) :
    Tendsto (fun h : ℝ => h⁻¹ *
        (w (x + X.X (Real.toNNReal h) ω) -
         w (x + X.X (Real.toNNReal h) ω - d * h)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have htime : Tendsto Real.toNNReal F (nhds (0 : ℝ≥0)) := by
    have hc := continuous_real_toNNReal.tendsto (0 : ℝ)
    simpa only [Real.toNNReal_zero] using hc.mono_left nhdsWithin_le_nhds
  have hwithin : Tendsto Real.toNNReal F
      (nhdsWithin (0 : ℝ≥0) (Ici 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨htime, Filter.Eventually.of_forall
      (fun h => Set.mem_Ici.mpr (show (0 : ℝ≥0) ≤ Real.toNNReal h from bot_le))⟩
  have hX : Tendsto (fun h : ℝ => X.X (Real.toNNReal h) ω)
      F (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, X.X_zero ω] using
      ((X.rightCont ω 0).tendsto.comp hwithin)
  have ha : Tendsto (fun h : ℝ => x + X.X (Real.toNNReal h) ω)
      F (nhds x) := by
    simpa only [add_zero] using tendsto_const_nhds.add hX
  have hz : Tendsto (fun h : ℝ => d * h) F (nhds (0 : ℝ)) := by
    have hh : Tendsto (fun h : ℝ => h) F (nhds (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using (tendsto_const_nhds.mul hh : 
      Tendsto (fun h : ℝ => d * h) F (nhds (d * 0)))
  have hb : Tendsto
      (fun h : ℝ => x + X.X (Real.toNNReal h) ω - d * h)
      F (nhds x) := by
    simpa only [sub_zero] using ha.sub hz
  exact avram_wave5_04c_C1_moving_base_drift_secant
    w hwC1 x d
    (fun h => x + X.X (Real.toNNReal h) ω)
    (fun h => x + X.X (Real.toNNReal h) ω - d * h)
    ha hb (fun h => by ring)
