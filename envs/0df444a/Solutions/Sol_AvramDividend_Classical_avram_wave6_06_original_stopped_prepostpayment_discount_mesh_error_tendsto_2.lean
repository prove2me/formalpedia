-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:58:27.699221+00:00
-- url     : https://prove2.me/submissions/396e5591-afc9-42bd-a668-534f85f4cf6d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ L * |s - t|)
    (hPre : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i + 1) : ℝ)))) *
          |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
            w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|)
      atTop (𝓝 0) := by
  let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
  have hvmono : ∀ n, Monotone (v n) := by
    intro n i j hij
    exact min_le_min (hu n hij) le_rfl
  have hvmesh : ∀ n i, i < k n →
      ((v n (i + 1) : ℝ) - (v n i : ℝ)) ≤ m n := by
    intro n i hi
    exact avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
      (u n) (hu n) i (τ ω) (m n) (hm n) (hmesh n i hi)
  have htotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (v n (k n)) ω - rightLimit D (v n 0) ω ≤ B :=
    avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
      D hD ω τ u k hzero
  simpa only [v] using
    avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
      X x D hD ω q hq w L hL a b hLip
      v hvmono k m hm hvmesh hPre hPost htotal hmesh0
