-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus18_original_shifted_bounded_random_count_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:27:06.82241+00:00
-- url     : https://prove2.me/submissions/000192ba-f4a8-4eb6-ad3e-e8d13755a890

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_shifted_physical_variance_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (H : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ ω, |H ω| ≤ L) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    AEStronglyMeasurable
        (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P →
      Integrable (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤ L ^ 2 * r := by
  intro B N r hMeas
  have hvariance :=
    avram_mix_annulus16_original_shifted_physical_variance_exact
      X s T n m hnm
  have hbase : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P :=
    hvariance.1
  have hmean :
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := hvariance.2
  have hbig : Integrable
      (fun ω => L ^ 2 * ((N ω).toReal - r) ^ 2) P :=
    hbase.const_mul (L ^ 2)
  have hle (ω : Ω) :
      (H ω * ((N ω).toReal - r)) ^ 2 ≤
        L ^ 2 * ((N ω).toReal - r) ^ 2 := by
    have hfac : (H ω) ^ 2 ≤ L ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr (hBound ω))
        (add_nonneg hL (abs_nonneg (H ω)))
      nlinarith [sq_abs (H ω)]
    calc
      (H ω * ((N ω).toReal - r)) ^ 2 =
          (H ω) ^ 2 * ((N ω).toReal - r) ^ 2 := by ring
      _ ≤ L ^ 2 * ((N ω).toReal - r) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
  have hweighted : Integrable
      (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P :=
    hbig.mono_nonneg hMeas
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      (Filter.Eventually.of_forall hle)
  refine ⟨hweighted, ?_⟩
  calc
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤
        ∫ ω, L ^ 2 * ((N ω).toReal - r) ^ 2 ∂P :=
      integral_mono hweighted hbig hle
    _ = L ^ 2 * r := by rw [integral_const_mul, hmean]
