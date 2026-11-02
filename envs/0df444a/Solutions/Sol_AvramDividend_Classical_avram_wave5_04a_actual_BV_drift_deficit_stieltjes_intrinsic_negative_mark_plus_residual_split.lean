-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:32:57.00522+00:00
-- url     : https://prove2.me/submissions/5ce9df4f-cba8-4a16-b311-9064acc76311

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Complete original BV drift-deficit Stieltjes interval mass is exactly
the genuine intrinsic negative source mark mass plus monotone residual
growth. The same physical Stieltjes function has precisely the actual
source negative jump at every singleton atom. No Ito--Meyer integration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ (F : StieltjesFunction ℝ≥0) (R : ℝ≥0 → ℝ),
      (∀ t : ℝ≥0,
        (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ t : ℝ≥0, 0 < t →
        F.measure {t} =
          ENNReal.ofReal (Function.leftLim
            (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        (F.measure (Ioc s t)).toReal =
          (∫⁻ p,
            (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal +
          (R t - R s) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump X hBV,
      avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
        X hBV] with ω hF hsource
  obtain ⟨F, hFdef, hFatom⟩ := hF
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hsource
  refine ⟨F, R, hFdef, hRdef, hRmono, hFatom, ?_⟩
  intro s t hst
  have hinc := hinterval s t hst
  have hJpos :
      0 ≤ (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))).toReal :=
    ENNReal.toReal_nonneg
  have hRpos : 0 ≤ R t - R s := sub_nonneg.mpr (hRmono hst)
  have hBbalance :
      ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) =
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal +
        (R t - R s) := by
    linarith only [hinc]
  have hBnonneg :
      0 ≤ ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) := by
    rw [hBbalance]
    exact add_nonneg hJpos hRpos
  have hFdiff :
      (F t : ℝ) - (F s : ℝ) =
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) := by
    rw [hFdef t, hFdef s]
  calc
    (F.measure (Ioc s t)).toReal =
        (ENNReal.ofReal ((F t : ℝ) - (F s : ℝ))).toReal := by
          rw [F.measure_Ioc]
    _ = ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) := by
          rw [hFdiff]
          exact ENNReal.toReal_ofReal hBnonneg
    _ = _ := hBbalance
