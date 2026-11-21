-- Prove2me | solution 2 for AvramDividend.Classical.avram_pj_workerC_original_fullmark_clipped_physical_grid_L2_uniform_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:40:51.504193+00:00
-- url     : https://prove2.me/submissions/ecc1f79c-4620-46f3-92dd-39eab6877031

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_uniform_physical_stopped_discounted_negative_mark_diagonal_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    (∀ i ∈ Finset.range m,
      Integrable (fun ω =>
        (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)^2) P) →
    (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) ≤
      K^2 * ((n : ℝ) *
        (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal) := by
  intro Δ grid N r H Z hHI
  let R : ℝ := (X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hRate (i : ℕ) : r i =
      ((n : ℝ) / ((m : ℝ) + 1)) * R := by
    exact avram_pj_workerC_original_uniform_physical_finite_mark_cell_rate_identity
      n m i (X.ν (Iic (-(1 / ((cut : ℝ) + 1)))))
  have hr : ∀ i ∈ Finset.range m, 0 ≤ r i := by
    intro i hi
    rw [hRate i]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _)
      (by positivity)) hR
  have hTotal : (∑ i ∈ Finset.range m, r i) ≤
      (n : ℝ) * R := by
    calc
      _ = ∑ i ∈ Finset.range m,
        ((n : ℝ) / ((m : ℝ) + 1)) * R := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hRate i
      _ ≤ (n : ℝ) * R :=
        avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
          n m R hR
  have hCoeff (i : ℕ) (hi : i ∈ Finset.range m)
      (ω : Ω) : |(if (ρ ω : WithTop ℝ≥0) ≤
      (grid i : WithTop ℝ≥0) then (0 : ℝ)
      else H i ω)| ≤ K := by
    by_cases hs : (ρ ω : WithTop ℝ≥0) ≤
        (grid i : WithTop ℝ≥0)
    · simpa only [if_pos hs, abs_zero] using hK
    · simp only [if_neg hs, H]
      apply abs_le.mpr
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
  obtain ⟨hDiagI, hDiag⟩ :=
    avram_pj_workerC_original_true_uniform_physical_stopped_discounted_negative_mark_diagonal_L2_energy
      X x D hD w q K hK cut ρ hρstop n m hn
  exact avram_pj_workerC_fullmark_grid_isometry_and_intensity_uniform_variance
    P m K ((n : ℝ) * R) hK r hr hTotal
    (fun i ω => if (ρ ω : WithTop ℝ≥0) ≤
      (grid i : WithTop ℝ≥0) then 0 else H i ω)
    Z hHI hCoeff hDiag
