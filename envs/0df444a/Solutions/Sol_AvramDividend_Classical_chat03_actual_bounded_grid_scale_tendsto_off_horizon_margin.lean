-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:47:56.74331+00:00
-- url     : https://prove2.me/submissions/4eece7d5-c854-4de2-82c3-340d9217ea84

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_exponential_discount_first_grid_scale_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Combine the proved strict-exit grid-scale convergence and proved no-exit
clock stabilisation with an arbitrary positive early-exit margin.
The continuous exit infimum is assumed different from the horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ε : ℝ≥0) (hε : 0 < ε)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hbranch : τ < T ∨ T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapBefore : τ < T →
      ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : T < τ →
      ∀ᶠ n in atTop,
        T ≤ (m n : ℝ≥0) * mesh n ∧
        (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  rcases hbranch with hbefore | hafter
  · have hfirst := chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
      X ω lower upper τ ε hτ hε mesh hmesh hpos m (hcapBefore hbefore) K hK
    exact chat03_exponential_discount_first_grid_scale_tendsto
      X q W hW hzero ω lower upper x τ T hτ
        mesh hmesh hpos (fun n => K n ω) hfirst
  · have hclock := chat03_noexit_before_passage_grid_cap_stabilises
      X ω lower upper τ T hτ hafter mesh m (hcapAfter hafter) K hK
    have heq :
      (fun _ : ℕ =>
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) =ᶠ[atTop]
      (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω)) := by
      filter_upwards [hclock] with n hn
      have hnT : T ≤ (K n ω : ℝ≥0) * mesh n := by
        calc
          T = min ((K n ω : ℝ≥0) * mesh n) T := hn.symm
          _ ≤ (K n ω : ℝ≥0) * mesh n := min_le_left _ _
      have hnReal : (T : ℝ) ≤ (((K n ω : ℝ≥0) : ℝ) * (mesh n : ℝ)) := by
        exact_mod_cast hnT
      simpa only [hn, min_eq_right hnReal]
    have hpost :
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop (𝓝 (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) :=
      tendsto_const_nhds.congr' heq
    have hafterReal : (T : ℝ) ≤ (τ : ℝ) :=
      NNReal.coe_le_coe.mpr (le_of_lt hafter)
    simpa [min_eq_right (le_of_lt hafter),
      min_eq_right hafterReal] using hpost