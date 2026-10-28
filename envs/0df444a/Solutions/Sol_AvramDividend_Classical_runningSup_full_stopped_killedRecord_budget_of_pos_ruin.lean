-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget_of_pos_ruin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:24:15.846586+00:00
-- url     : https://prove2.me/submissions/b39fb614-bbc5-4871-9750-0753ef1175ba

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_surviving_finite_horizon_killedRecord_budget
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_lintegral_Ico_le_Ioc_of_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (hτ : 0 < τ) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by 
  apply paymentTimes_lintegral_le_of_rational_prefix_bounds _ _ τ _ hτ
  rintro ⟨r, hr0, hrτ⟩
  refine le_trans (lintegral_Ico_le_Ioc_of_zero_initial_atom _ _ _
    (runningSup_dividendMeasure_zero_initial_atom X 0 le_rfl ω)) ?_
  refine le_trans (le_of_eq ?_) (runningSup_surviving_finite_horizon_killedRecord_budget X ω τ q h hq hh
    (r : ℝ).toNNReal hrτ)
  have hsub : Set.Ioc (0 : ℝ) ((r : ℝ).toNNReal : ℝ) ⊆ paymentTimes τ := by
    intro x hx
    refine ⟨hx.1.le, Or.inr (lt_of_le_of_lt ?_ hrτ)⟩
    have : x ≤ (r : ℝ) := by
      have := hx.2; rwa [Real.coe_toNNReal _ hr0.le] at this
    exact ENNReal.ofReal_le_ofReal this
  rw [Real.coe_toNNReal _ hr0.le] at hsub ⊢
  have : (fun x : ℝ => if x ∈ Set.Ioc (0 : ℝ) (r : ℝ) then ENNReal.ofReal (Real.exp (-(q * x))) else 0)
      = (Set.Ioc (0 : ℝ) (r : ℝ)).indicator (fun x => ENNReal.ofReal (Real.exp (-(q * x)))) := by
    funext x; simp [Set.indicator]
  rw [this, lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 hsub]
