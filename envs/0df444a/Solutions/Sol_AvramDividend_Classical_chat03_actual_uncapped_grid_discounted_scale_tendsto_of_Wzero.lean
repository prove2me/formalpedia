-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:51:56.861966+00:00
-- url     : https://prove2.me/submissions/aa0cd80a-2697-4ac6-b6e0-e90eee69e275

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_clock_tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.NNReal.Defs
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Remove the finite-time cap from the exact discounted bounded-grid
scale reward whenever the continuous strict exit occurs before the cap.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτT : τ < T)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
        W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω))
      atTop
      (𝓝 (Real.exp (-(q * (τ : ℝ))) *
        W (x + X.X τ ω))) := by
  have hclock :=
    chat03_actual_hittingBtwn_clock_tendsto
      X ω lower upper τ hτ mesh hmesh hpos m hcap K hK
  have hbefore : ∀ᶠ n in atTop, (K n ω : ℝ≥0) * mesh n < T :=
    (tendsto_order.1 hclock).2 T hτT
  have hcapped :=
    chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
      X q W hW hzero ω lower upper x τ T hτ
        mesh hmesh hpos m hcap K hK
  have heq :
      (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω)) =ᶠ[atTop]
      (fun n =>
        Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
          W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω)) := by
    filter_upwards [hbefore] with n hn
    have hnReal :
        (((K n ω : ℝ≥0) * mesh n) : ℝ) ≤ (T : ℝ) :=
      NNReal.coe_le_coe.mpr (le_of_lt hn)
    simp [min_eq_left (le_of_lt hn), hnReal] <;>
      exact Or.inl (Or.inl hnReal)
  have hτReal : (τ : ℝ) ≤ (T : ℝ) :=
    NNReal.coe_le_coe.mpr (le_of_lt hτT)
  simpa [min_eq_left (le_of_lt hτT), min_eq_left hτReal] using
    hcapped.congr' heq
