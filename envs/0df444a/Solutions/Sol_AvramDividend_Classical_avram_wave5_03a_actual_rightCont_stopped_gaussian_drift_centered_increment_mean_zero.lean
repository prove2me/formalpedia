-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:25:51.198945+00:00
-- url     : https://prove2.me/submissions/e439cf0a-d3fd-4da9-bc14-b24f5172c553

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Mean zero of the genuine stopped Gaussian source increment, by shifted Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let C : ℝ := (h : ℝ) * X.σ ^ 2
  change (∫ ω, Y ω ∂P) = 0
  have hMem : MemLp Y 2 P := by
    simpa only [Y] using
      (avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
        X hν τ hτ T hbounded h)
  have hYi : Integrable Y P :=
    hMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hSq : Integrable (fun ω => (Y ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
  have hShiftI (a : ℝ) : Integrable (fun ω => (Y ω + a) ^ 2) P := by
    have heq : (fun ω => (Y ω + a) ^ 2) =
        (fun ω => (Y ω) ^ 2 + (2 * a) * Y ω + a ^ 2) := by
      funext ω; ring
    rw [heq]
    exact (hSq.add (hYi.const_mul (2 * a))).add (integrable_const (a ^ 2))
  have hBound (a : ℝ) :
      (∫ ω, (Y ω + a) ^ 2 ∂P) ≤ C + a ^ 2 := by
    have hb := avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy
      X hν τ hτ T hbounded h a
    change (∫⁻ ω, ENNReal.ofReal ((Y ω + a) ^ 2) ∂P) ≤
      ENNReal.ofReal (C + a ^ 2) at hb
    have he : (∫⁻ ω, ENNReal.ofReal ((Y ω + a) ^ 2) ∂P) =
        ENNReal.ofReal (∫ ω, (Y ω + a) ^ 2 ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal (hShiftI a)
        (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω + a)))).symm
    rw [he] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by dsimp [C]; positivity)).mp hb
  have hExpand (a : ℝ) :
      (∫ ω, (Y ω + a) ^ 2 ∂P) =
        (∫ ω, (Y ω) ^ 2 ∂P) + 2 * a * (∫ ω, Y ω ∂P) + a ^ 2 := by
    calc
      (∫ ω, (Y ω + a) ^ 2 ∂P) =
          ∫ ω, ((Y ω) ^ 2 + ((2 * a) * Y ω + a ^ 2)) ∂P := by
        congr 1
        funext ω
        ring
      _ = (∫ ω, (Y ω) ^ 2 ∂P) +
          (∫ ω, ((2 * a) * Y ω + a ^ 2) ∂P) :=
        integral_add hSq ((hYi.const_mul (2 * a)).add (integrable_const (a ^ 2)))
      _ = (∫ ω, (Y ω) ^ 2 ∂P) + 2 * a * (∫ ω, Y ω ∂P) + a ^ 2 := by
        rw [integral_add (hYi.const_mul (2 * a)) (integrable_const (a ^ 2))]
        rw [integral_const_mul]
        simp
        ring
  by_contra hne
  let v : ℝ := ∫ ω, Y ω ∂P
  let A : ℝ := C - ∫ ω, (Y ω) ^ 2 ∂P
  have hv : v ≠ 0 := by simpa only [v] using hne
  have hd : 2 * v ≠ 0 := mul_ne_zero (by norm_num) hv
  let a : ℝ := (A + 1) / (2 * v)
  have ha : 2 * a * v = A + 1 := by
    dsimp [a]
    field_simp [hd]
  have hb := hBound a
  rw [hExpand a] at hb
  have ha' : 2 * a * (∫ ω, Y ω ∂P) = C - (∫ ω, (Y ω) ^ 2 ∂P) + 1 := by
    simpa only [A, v] using ha
  nlinarith [ha']
