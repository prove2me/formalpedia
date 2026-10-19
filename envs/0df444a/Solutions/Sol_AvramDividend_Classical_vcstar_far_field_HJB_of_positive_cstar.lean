-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_far_field_HJB_of_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:57:44.037306+00:00
-- url     : https://prove2.me/submissions/aaf42d73-cf00-45b0-926f-0c1c71c19d0e

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_residual_nonpos_of_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_qvalue_dominates_drift_far_positive_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg_of_pos
import Theorems.Thm_AvramDividend_Classical_barrierValue_monotone_of_divE_monotone_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := hpos
  have hd : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg_of_pos X q W hW a ha
  have hwmono : Monotone W := scaleFunction_monotone X q W hW
  have hdiv : ∀ z : ℝ,
      divE (W z) (scaleDeriv W a) = W z / deriv W a := by
    intro z
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp [divE, scaleDeriv, ha0]
  have hbranchmono : MonotoneOn
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) (Ici 0) := by
    intro u hu v hv huv
    change divE (W u) (scaleDeriv W a) ≤
      divE (W v) (scaleDeriv W a)
    rw [hdiv u, hdiv v]
    exact div_le_div_of_nonneg_right (hwmono huv) hd
  have hbranchnonneg : ∀ z : ℝ, 0 ≤ z →
      0 ≤ divE (W z) (scaleDeriv W a) := by
    intro z hz
    rw [hdiv z]
    exact div_nonneg (hW.2.1 z hz) hd
  have hmono : Monotone (vcstar W) := by
    change Monotone (barrierValue W a)
    exact barrierValue_monotone_of_divE_monotone_nonneg
      W a (le_of_lt ha) hbranchmono hbranchnonneg
  have hm : 0 ≤ max 0 (X.c / q) := le_max_left _ _
  have hx : (cstar W).toReal < x := by linarith
  have hfar1 : (cstar W).toReal + 1 ≤ x := by linarith
  have hvalue : X.c ≤ q * vcstar W x :=
    vcstar_qvalue_dominates_drift_far_positive_barrier
      X q hq W hW hpos x hfar
  obtain ⟨hint, hres⟩ :=
    vcstar_far_field_generator_residual_nonpos_of_monotone
      X q W hW hmono x hfar1 hvalue
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  refine ⟨hint, ?_⟩
  rw [hder]
  simpa using (max_eq_right hres :
    max (X.generator (vcstar W) x - q * vcstar W x) 0 = 0)
