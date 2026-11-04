-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_L2_two_sided_signed_martingale_mean_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:17:36.572088+00:00
-- url     : https://prove2.me/submissions/68ea02cd-b83b-4fb2-a22d-6861292dfd1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform quadratic estimates for both signs retain zero mean at the original stopped limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Mk : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hPosMeas : ∀ k, AEStronglyMeasurable (fun ω => max (Mk k ω) 0) P)
    (hNegMeas : ∀ k, AEStronglyMeasurable (fun ω => max (-(Mk k ω)) 0) P)
    (hPosMMeas : AEStronglyMeasurable (fun ω => max (M ω) 0) P)
    (hNegMMeas : AEStronglyMeasurable (fun ω => max (-(M ω)) 0) P)
    (hPosConv : ∀ᵐ ω ∂P, Tendsto (fun k => max (Mk k ω) 0) atTop (𝓝 (max (M ω) 0)))
    (hNegConv : ∀ᵐ ω ∂P, Tendsto (fun k => max (-(Mk k ω)) 0) atTop (𝓝 (max (-(M ω)) 0)))
    (C : ℝ) (hC : 0 ≤ C)
    (hPos2 : ∀ k, Integrable (fun ω => (max (Mk k ω) 0) ^ 2) P ∧
      (∫ ω, (max (Mk k ω) 0) ^ 2 ∂P) ≤ C)
    (hNeg2 : ∀ k, Integrable (fun ω => (max (-(Mk k ω)) 0) ^ 2) P ∧
      (∫ ω, (max (-(Mk k ω)) 0) ^ 2 ∂P) ≤ C)
    (hZeroSplit : ∀ k, (∫ ω, max (Mk k ω) 0 ∂P) -
      (∫ ω, max (-(Mk k ω)) 0 ∂P) = 0) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  have hPos0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ max (Mk k ω) 0 := by
    intro k
    exact Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hNeg0 : ∀ k, ∀ᵐ ω ∂P, 0 ≤ max (-(Mk k ω)) 0 := by
    intro k
    exact Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  obtain ⟨hPosI, hPosLim⟩ :=
    nonnegative_integral_tendsto_of_uniform_second_moment
      (fun k ω => max (Mk k ω) 0) (fun ω => max (M ω) 0)
      hPosMeas hPos0 hPosMMeas hPosConv C hC hPos2
  obtain ⟨hNegI, hNegLim⟩ :=
    nonnegative_integral_tendsto_of_uniform_second_moment
      (fun k ω => max (-(Mk k ω)) 0) (fun ω => max (-(M ω)) 0)
      hNegMeas hNeg0 hNegMMeas hNegConv C hC hNeg2
  have hdecomp (y : ℝ) : max y 0 - max (-y) 0 = y := by
    rcases le_total 0 y with hy | hy
    · rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]
      ring
    · rw [max_eq_right hy, max_eq_left (neg_nonneg.mpr hy)]
      ring
  have hDec : (fun ω => max (M ω) 0 - max (-(M ω)) 0) = M := by
    funext ω
    exact hdecomp (M ω)
  have hMInt : Integrable M P := by
    rw [← hDec]
    exact hPosI.sub hNegI
  have hLimit := hPosLim.sub hNegLim
  have hZero : Tendsto
      (fun k => (∫ ω, max (Mk k ω) 0 ∂P) -
        (∫ ω, max (-(Mk k ω)) 0 ∂P)) atTop (𝓝 (0 : ℝ)) := by
    have hEq : (fun k => (∫ ω, max (Mk k ω) 0 ∂P) -
        (∫ ω, max (-(Mk k ω)) 0 ∂P)) = (fun _ : ℕ => (0 : ℝ)) := by
      funext k
      exact hZeroSplit k
    rw [hEq]
    exact tendsto_const_nhds
  have hEqMeans := tendsto_nhds_unique hLimit hZero
  refine ⟨hMInt, ?_⟩
  rw [← hDec, integral_sub hPosI hNegI]
  exact hEqMeans