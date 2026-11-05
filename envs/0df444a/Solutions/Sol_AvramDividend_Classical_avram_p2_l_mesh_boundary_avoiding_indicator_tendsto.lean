-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:57:06.063546+00:00
-- url     : https://prove2.me/submissions/e02f3aba-538d-47c8-a4ee-9718a4737de8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_full_grid_local_mark_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_indicator_continuous_at_interior_side

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- A separated negative Borel indicator has genuine full-grid convergence
when all significant true marks lie off its topological boundary. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hBsep : B ⊆ Set.Iic (-ρ))
    (hlocal : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ∈ interior B ∨
        Y u - Function.leftLim Y u ∈ interior (Bᶜ))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          B.indicator (fun _ : ℝ => (1 : ℝ))
            (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ S,
          B.indicator (fun _ : ℝ => (1 : ℝ))
            (Y u - Function.leftLim Y u))) := by
  classical
  have hzero : ∀ z : ℝ, |z| < ρ →
      B.indicator (fun _ : ℝ => (1 : ℝ)) z = 0 := by
    intro z hz
    have hzB : z ∉ B := by
      intro hzB
      have hUpper : z ≤ -ρ := hBsep hzB
      have hLower : -ρ < z := (abs_lt.mp hz).1
      exact (not_lt_of_ge hUpper) hLower
    simp [Set.indicator, hzB]
  have hcont : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      ContinuousAt (B.indicator (fun _ : ℝ => (1 : ℝ)))
        (Y u - Function.leftLim Y u) := by
    intro u hu0 huT huρ
    exact avram_p2_l_mesh_indicator_continuous_at_interior_side
      B _ (hlocal u hu0 huT huρ)
  exact avram_p2_l_mesh_full_grid_local_mark_continuity
    Y T hT (B.indicator (fun _ : ℝ => (1 : ℝ)))
    ρ hρ hzero hcont hL hR
