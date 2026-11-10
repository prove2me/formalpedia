-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:08:08.306081+00:00
-- url     : https://prove2.me/submissions/e6e69e6c-b3e2-4941-8aff-8664bf4d688a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_real_window_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section
/-- Same-source stopped clipped derivative annulus compensated martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cutLo cutHi : ℕ) (hCut : cutLo ≤ cutHi)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (n : ℕ) :
    let B : Set ℝ := Ioc (-(1 / ((cutLo : ℝ) + 1)))
      (-(1 / ((cutHi : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by
  classical
  let c : ℝ := -(1 / ((cutLo : ℝ) + 1))
  let d : ℝ := -(1 / ((cutHi : ℝ) + 1))
  let B : Set ℝ := Ioc c d
  let J : ℕ → Set ℝ → Ω → ℝ≥0∞ := fun i E ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (grid i) (grid (i + 1)) ×ˢ E)
  let rate : ℕ → Set ℝ → ℝ := fun i E =>
    (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν E).toReal
  let H : ℕ → Ω → ℝ := fun i ω =>
    max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
      deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (grid i))))
  let Z : ℕ → Set ℝ → Ω → ℝ := fun i E ω =>
    (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then (0 : ℝ) else H i ω) * ((J i E ω).toReal - rate i E)
  change MemLp (fun ω => ∑ i ∈ Finset.range n, Z i B ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i B ω ∂P) = 0
  have hLo := avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
    X x D hD w q K hK cutLo τ hτstop grid hGrid n
  have hHi := avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
    X x D hD w q K hK cutHi τ hτstop grid hGrid n
  change MemLp (fun ω => ∑ i ∈ Finset.range n, Z i (Iic c) ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i (Iic c) ω ∂P) = 0 at hLo
  change MemLp (fun ω => ∑ i ∈ Finset.range n, Z i (Iic d) ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i (Iic d) ω ∂P) = 0 at hHi
  have hCell (i : ℕ) (ω : Ω) :
      Z i B ω = Z i (Iic d) ω - Z i (Iic c) ω := by
    have hCount := avram_mix_annulus15_original_real_window_count_additive X ω (grid i) (grid (i + 1)) (hGrid i) cutLo cutHi hCut
    change (J i (Iic d) ω).toReal = (J i (Iic c) ω).toReal + (J i B ω).toReal at hCount
    have hRate := avram_mixed_source13_original_annulus_levy_rate_difference X (grid (i + 1) - grid i) cutLo cutHi hCut
    change rate i (Iic d) = rate i (Iic c) + rate i B at hRate
    dsimp [Z]; rw [hCount, hRate]; ring
  have hSum (ω : Ω) :
      (∑ i ∈ Finset.range n, Z i B ω) =
        (∑ i ∈ Finset.range n, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range n, Z i (Iic c) ω) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i hi => hCell i ω)
  constructor
  · have hEq : (fun ω => ∑ i ∈ Finset.range n, Z i B ω) =
        (fun ω => (∑ i ∈ Finset.range n, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range n, Z i (Iic c) ω)) := by
      funext ω
      exact hSum ω
    rw [hEq]
    exact hHi.1.sub hLo.1
  · calc
      (∫ ω, ∑ i ∈ Finset.range n, Z i B ω ∂P) =
        (∫ ω, (∑ i ∈ Finset.range n, Z i (Iic d) ω) -
          (∑ i ∈ Finset.range n, Z i (Iic c) ω) ∂P) := by
            exact integral_congr_ae (Filter.Eventually.of_forall hSum)
      _ = (∫ ω, ∑ i ∈ Finset.range n, Z i (Iic d) ω ∂P) -
          (∫ ω, ∑ i ∈ Finset.range n, Z i (Iic c) ω ∂P) :=
            integral_sub (hHi.1.integrable (by norm_num))
              (hLo.1.integrable (by norm_num))
      _ = 0 := by rw [hHi.2, hLo.2]; ring
