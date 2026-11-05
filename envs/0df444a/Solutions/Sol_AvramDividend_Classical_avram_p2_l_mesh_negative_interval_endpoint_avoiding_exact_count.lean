-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_negative_interval_endpoint_avoiding_exact_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:47:20.78714+00:00
-- url     : https://prove2.me/submissions/acbbb5d0-cc5c-4839-a961-5d9dd29e8d25

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_counts_eventually_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- For a negative half-open interval, no true significant jump at either
endpoint suffices for eventual exact counts on the original uniform mesh. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (a b ρ : ℝ) (hρ : 0 < ρ) (hbneg : b ≤ -ρ)
    (hEndpoint : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      ρ ≤ |Y u - Function.leftLim Y u| →
      Y u - Function.leftLim Y u ≠ a ∧
        Y u - Function.leftLim Y u ≠ b)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop,
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ Ioc a b)).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈ Ioc a b)).card := by
  classical
  have hBsep : Ioc a b ⊆ Iic (-ρ) := by
    intro z hz
    exact le_trans hz.2 hbneg
  have hlocal (u : ℝ≥0) (hu0 : 0 < u) (huT : u ≤ T)
      (huρ : ρ ≤ |Y u - Function.leftLim Y u|) :
      Y u - Function.leftLim Y u ∈ interior (Ioc a b) ∨
        Y u - Function.leftLim Y u ∈ interior ((Ioc a b)ᶜ) := by
    let z : ℝ := Y u - Function.leftLim Y u
    have hne : z ≠ a ∧ z ≠ b := hEndpoint u hu0 huT huρ
    by_cases ha : a < z
    · by_cases hb : z < b
      · left
        have hsubset : Ioo a b ⊆ Ioc a b := by
          intro x hx
          exact ⟨hx.1, le_of_lt hx.2⟩
        apply mem_interior_iff_mem_nhds.mpr
        exact Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds ⟨ha, hb⟩) hsubset
      · right
        have hgt : b < z :=
          lt_of_le_of_ne (le_of_not_gt hb) hne.2.symm
        have hsubset : Ioi b ⊆ (Ioc a b)ᶜ := by
          intro x hx hxB
          exact (not_le_of_gt hx) hxB.2
        apply mem_interior_iff_mem_nhds.mpr
        exact Filter.mem_of_superset
          (isOpen_Ioi.mem_nhds hgt) hsubset
    · right
      have hlt : z < a :=
        lt_of_le_of_ne (le_of_not_gt ha) hne.1
      have hsubset : Iio a ⊆ (Ioc a b)ᶜ := by
        intro x hx hxB
        exact (not_lt_of_ge (le_of_lt hx)) hxB.1
      apply mem_interior_iff_mem_nhds.mpr
      exact Filter.mem_of_superset
        (isOpen_Iio.mem_nhds hlt) hsubset
  simpa using (avram_p2_l_mesh_boundary_counts_eventually_exact
    Y T hT (Ioc a b) ρ hρ hBsep hlocal hL hR)
