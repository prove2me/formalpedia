-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_pathwise_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:24:47.272431+00:00
-- url     : https://prove2.me/submissions/708c8988-d18d-4015-93b0-39f9eb88ee2b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

/-- Physical jump-cell counts recover a finite original-path weighted sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a b : Fin n → ℝ≥0) (B : Fin n → Set ℝ)
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : Fin n → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (a i) (b i) ×ˢ B i))
    (jumpTimes : Ω → Finset ℝ≥0)
    (cell : ℝ≥0 → Fin n)
    (hCount : ∀ ω i, (N i ω).toReal =
      (((jumpTimes ω).filter (fun u => cell u = i)).card : ℝ))
    (H : Fin n → Ω → ℝ) (ω : Ω) :
    (∑ i : Fin n, H i ω * (N i ω).toReal) =
      ∑ u ∈ jumpTimes ω, H (cell u) ω := by
  classical
  have hCard (i : Fin n) :
      (((jumpTimes ω).filter (fun u => cell u = i)).card : ℝ) =
      ∑ u ∈ jumpTimes ω, if cell u = i then (1 : ℝ) else 0 := by
    have hNat := Finset.card_filter (fun u => cell u = i) (jumpTimes ω)
    exact_mod_cast hNat
  calc
    (∑ i : Fin n, H i ω * (N i ω).toReal) =
        ∑ i : Fin n, ∑ u ∈ jumpTimes ω,
          if cell u = i then H i ω else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hCount ω i, hCard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> simp
    _ = ∑ u ∈ jumpTimes ω, ∑ i : Fin n,
          if cell u = i then H i ω else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ jumpTimes ω, H (cell u) ω := by
      apply Finset.sum_congr rfl
      intro u hu
      simp
