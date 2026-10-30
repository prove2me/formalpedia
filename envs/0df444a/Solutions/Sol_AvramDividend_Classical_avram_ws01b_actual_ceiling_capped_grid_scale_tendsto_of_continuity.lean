-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:28:56.328923+00:00
-- url     : https://prove2.me/submissions/b6a74bc9-c7e5-4cd4-b7e7-b8abe8fa7be8

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Theorems.Thm_AvramDividend_Classical_chat03_terminal_ceiling_cap_before_later_exit
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_terminal_tie_clock_eq_horizon
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

/-- Ceiling-grid q-scale payoffs converge at every terminal configuration,
provided the scale is continuous only at the actual stopped reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hContinuousEarly : τ < T → ContinuousAt W (x + X.X τ ω))
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
  have hdiscount : Continuous (fun t : ℝ≥0 =>
      Real.exp (-(q * (t : ℝ)))) :=
    Real.continuous_exp.comp
      ((continuous_const.mul NNReal.continuous_coe).neg)
  have hcapT :
      ∀ᶠ n in atTop,
        T ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n := by
    filter_upwards with n
    exact (chat03_nnreal_grid_ceiling_bracket
      T (mesh n) (hpos n)).1
  rcases lt_trichotomy τ T with hbefore | htie | hafter
  · have hε : 0 < T - τ := tsub_pos_of_lt hbefore
    have hsum : τ + (T - τ) = T := by
      simpa only [add_comm] using
        (tsub_add_cancel_of_le (le_of_lt hbefore))
    have hcapBefore :
        ∀ᶠ n in atTop,
          τ + (T - τ) ≤
            (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n := by
      filter_upwards [hcapT] with n hn
      simpa only [hsum] using hn
    have hfirst := chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
      X ω lower upper τ (T - τ) hτ hε mesh hmesh hpos
      (fun n => Nat.ceil (T / mesh n)) hcapBefore K hK
    have hcont : ContinuousAt W (x + X.X (min τ T) ω) := by
      simpa only [min_eq_left hbefore.le] using hContinuousEarly hbefore
    exact avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
      X q W hW ω lower upper x τ T hτ
      _ hdiscount hcont mesh hmesh hpos (fun n => K n ω) hfirst
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
  · have hcapAfter :
        ∀ᶠ n in atTop,
          T ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n ∧
          (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n < τ := by
      filter_upwards
        [chat03_terminal_ceiling_cap_before_later_exit
          T τ hafter mesh hmesh hpos] with n hn
      exact hn
    have hclock := chat03_noexit_before_passage_grid_cap_stabilises
      X ω lower upper τ T hτ hafter mesh
      (fun n => Nat.ceil (T / mesh n)) hcapAfter K hK
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
      have hnReal : (T : ℝ) ≤
          (((K n ω : ℝ≥0) : ℝ) * (mesh n : ℝ)) := by
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
