-- Prove2me | solution 1 for AvramDividend.Classical.discounted_exponential_levy_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:06:40.480381+00:00
-- url     : https://prove2.me/submissions/5f5b953d-44da-4849-a7bc-2a11802e0036

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_martingale_antitone_weight_supermartingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * q)) 𝓕 P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let c : ℝ≥0 → ℝ := fun t =>
    Real.exp ((t : ℝ) * (X.ψ θ - q))
  have hZ : Martingale Z 𝓕 P :=
    levy_compensated_exponential_martingale X θ hθ
  have hZnonneg : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ Z t ω := by
    intro t
    filter_upwards [] with ω
    exact (Real.exp_pos _).le
  have hc : Antitone c := by
    intro s t hst
    dsimp [c]
    apply Real.exp_le_exp.mpr
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    exact mul_le_mul_of_nonpos_right hst' (sub_nonpos.mpr hψ)
  have hS :=
    martingale_antitone_weight_supermartingale Z hZ hZnonneg c hc
  have heq :
      (fun t ω => c t * Z t ω) =
      (fun t ω => Real.exp (θ * X.X t ω - (t : ℝ) * q)) := by
    funext t ω
    dsimp [c, Z]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hS
  exact hS
