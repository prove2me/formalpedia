-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:17:30.66334+00:00
-- url     : https://prove2.me/submissions/820c9e08-0c29-43ef-94cd-9c16824d91e5

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_terminal_tie_clock_eq_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Actual ceiling-capped grid stopped-scale convergence for every finite
continuous strict exit infimum, including an exit precisely at T.
The strict branches reuse the accepted theorem. The equality branch
uses exact clipped-grid clock equality and constant-sequence convergence.
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
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  rcases lt_trichotomy τ T with hbefore | htie | hafter
  · exact chat03_actual_ceiling_capped_grid_scale_tendsto
      X q W hW hzero ω lower upper x τ T hτ (Or.inl hbefore)
      mesh hmesh hpos K hK
  · subst τ
    have hc (n : ℕ) :
        min ((K n ω : ℝ≥0) * mesh n) T = T := by
      rw [hK n ω]
      exact chat03_actual_grid_terminal_tie_clock_eq_horizon
        X ω lower upper T (mesh n) (Nat.ceil (T / mesh n))
        hτ (chat03_nnreal_grid_ceiling_bracket T (mesh n) (hpos n)).1
    have hconst :
        (fun n =>
          Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω)) =
        (fun _ : ℕ => Real.exp (-(q * (T : ℝ))) *
          W (x + X.X T ω)) := by
      funext n
      have hreal :
          min (((K n ω : ℝ≥0) : ℝ) * (mesh n : ℝ)) (T : ℝ) =
            (T : ℝ) := by
        have heq := congrArg (fun z : ℝ≥0 => (z : ℝ)) (hc n)
        simpa only [NNReal.coe_min, NNReal.coe_mul] using heq
      rw [hc n, hreal]
    simpa only [hconst, min_self] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Real.exp (-(q * (T : ℝ))) *
          W (x + X.X T ω)) atTop
          (𝓝 (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))))
  · exact chat03_actual_ceiling_capped_grid_scale_tendsto
      X q W hW hzero ω lower upper x τ T hτ (Or.inr hafter)
      mesh hmesh hpos K hK
