-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_predictable_grid_from_conditional_diagonals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:58:02.058285+00:00
-- url     : https://prove2.me/submissions/5dfdda03-e9d6-4fd9-be31-688e314dd43d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

/-- Genuine original intrinsic finite-grid predictable L² isometry from source conditional diagonal moments. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1)) (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε)) (hν : ∀ i, X.ν (B i) < ⊤) (N : ℕ → Ω → ℝ≥0∞) (hActual : ∀ i, N i = fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (grid i) (grid (i + 1)) ×ˢ B i)) (hMeas : ∀ i, Measurable (N i)) (r : ℕ → ℝ) (hRate : ∀ i, r i = (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) (H D : ℕ → Ω → ℝ) (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i)) (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i)) (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)] (fun ω => ∑ j ∈ Finset.range i, D j ω)) (hPairL2 : ∀ i, MemLp (fun ω => (∑ j ∈ Finset.range i, D j ω) * H i ω) 2 P) (hCountL2 : ∀ i, MemLp (fun ω => (N i ω).toReal - r i) 2 P) (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2) | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i)) (hSq : ∀ i, Integrable (fun ω => ((N i ω).toReal - r i) ^ 2) P) (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P) (hWSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P) (hPrefixSq : ∀ i, Integrable (fun ω => (∑ j ∈ Finset.range i, D j ω) ^ 2) P) (n : ℕ) :
  (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) = ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  letI : MeasurableSpace Ω := mΩ
  have hCross (i : ℕ) :
      (∫ ω, (∑ j ∈ Finset.range i, D j ω) * D i ω ∂P) = 0 := by
    have hz := avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (B i) (hB i) (hBand i) (hν i)
      (N i) (hActual i) (hMeas i)
      (fun ω => ∑ j ∈ Finset.range i, D j ω) (H i)
      (hPrefix i) (hH i) (hPairL2 i)
      (by simpa only [hRate i] using hCountL2 i)
    simpa only [hD i, hRate i] using hz
  have hDiag (i : ℕ) :
      (∫ ω, (D i ω) ^ 2 ∂P) =
        r i * ∫ ω, (H i ω) ^ 2 ∂P := by
    have hd := avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (B i) (hB i) (hBand i) (hν i)
      (N i) (hActual i) (r i) (hRate i) (hSecond i)
      (H i) (hH i) (hSq i) (hHSq i) (hWSq i)
    simpa only [hD i] using hd
  induction n with
  | zero => simp
  | succ n ih =>
    have hCrossInt : Integrable (fun ω =>
        (∑ j ∈ Finset.range n, D j ω) * D n ω) P := by
      have hi := (hPairL2 n).integrable_mul (hCountL2 n)
      convert hi using 1
      funext ω
      simp only [Pi.mul_apply, hD n ω]
      ring
    have hDSq : Integrable (fun ω => (D n ω) ^ 2) P := by
      simpa only [hD n, mul_pow] using (hWSq n)
    simp only [Finset.sum_range_succ]
    calc
      (∫ ω, ((∑ i ∈ Finset.range n, D i ω) + D n ω) ^ 2 ∂P) =
          (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) +
            2 * (∫ ω, (∑ i ∈ Finset.range n, D i ω) * D n ω ∂P) +
            (∫ ω, (D n ω) ^ 2 ∂P) := by
        calc
          (∫ ω, ((∑ i ∈ Finset.range n, D i ω) + D n ω) ^ 2 ∂P) =
              (∫ ω, ((∑ i ∈ Finset.range n, D i ω) ^ 2 +
                2 * ((∑ i ∈ Finset.range n, D i ω) * D n ω) +
                (D n ω) ^ 2) ∂P) := by
                congr 1
                funext ω
                ring
          _ = (∫ ω, ((∑ i ∈ Finset.range n, D i ω) ^ 2 +
                2 * ((∑ i ∈ Finset.range n, D i ω) * D n ω)) ∂P) +
              (∫ ω, (D n ω) ^ 2 ∂P) := by
                exact integral_add ((hPrefixSq n).add (hCrossInt.const_mul 2)) hDSq
          _ = ((∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) +
              (∫ ω, 2 * ((∑ i ∈ Finset.range n, D i ω) * D n ω) ∂P)) +
              (∫ ω, (D n ω) ^ 2 ∂P) := by
                congr 1
                exact integral_add (hPrefixSq n) (hCrossInt.const_mul 2)
          _ = (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) +
              2 * (∫ ω, (∑ i ∈ Finset.range n, D i ω) * D n ω ∂P) +
              (∫ ω, (D n ω) ^ 2 ∂P) := by
                congr 2
                simp only [integral_const_mul]
      _ = (∑ i ∈ Finset.range n,
            r i * ∫ ω, (H i ω) ^ 2 ∂P) +
            r n * ∫ ω, (H n ω) ^ 2 ∂P := by
        rw [hCross n, hDiag n, ih]
        ring
