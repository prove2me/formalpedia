-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_grid_quadratic_energy_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:26:24.427626+00:00
-- url     : https://prove2.me/submissions/8999bc09-2656-49fc-8bfb-8a7db1ba2fd0

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ i ω, |H i ω| ≤ L)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) ≤
      (∑ i ∈ Finset.range n, r i) * L ^ 2 := by
  have hIso :=
    avram_p4_s3_interval_e_original_physical_grid_isometry_l2_integrability_auto
      X T cut grid hGrid hTime ε hε B hB hBand hCut hν N hActual
      r hRate H D hD hH hHL2 L hBound hPrefix hSecond n
  rw [hIso]
  calc
    (∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P)
        ≤ ∑ i ∈ Finset.range n, r i * L ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left
          · have hInt : Integrable (fun ω => (H i ω) ^ 2) P :=
              (hHL2 i).integrable_sq
            have hBdd (ω : Ω) : (H i ω) ^ 2 ≤ L ^ 2 := by
              have hprod : 0 ≤
                  (L - |H i ω|) * (L + |H i ω|) :=
                mul_nonneg (sub_nonneg.mpr (hBound i ω))
                  (add_nonneg hL (abs_nonneg _))
              nlinarith [sq_abs (H i ω)]
            have hle : (∫ ω, (H i ω) ^ 2 ∂P) ≤
                (∫ _ : Ω, L ^ 2 ∂P) :=
              integral_mono hInt (integrable_const _) hBdd
            simpa using hle
          · rw [hRate i]
            exact ENNReal.toReal_nonneg
    _ = (∑ i ∈ Finset.range n, r i) * L ^ 2 := by
      rw [Finset.sum_mul]
