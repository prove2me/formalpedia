-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_boundary_counts_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:23:20.827069+00:00
-- url     : https://prove2.me/submissions/07907025-2dac-4d48-9290-9613a206bcdc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_nat_count_stabilises_of_real_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators
open scoped Classical

/-- Away from genuine jump-mark boundaries, sufficiently fine uniform
meshes count exactly the same negative-band jumps as the intrinsic path. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hBsep : B ⊆ Iic (-ρ))
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
      ∀ᶠ n : ℕ in atTop,
        ((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card =
        (S.filter (fun u => Y u - Function.leftLim Y u ∈ B)).card := by
  classical
  obtain ⟨S, hS, hlim⟩ :=
    avram_p2_l_mesh_boundary_avoiding_indicator_tendsto
      Y T hT B ρ hρ hBsep hlocal hL hR
  have hcountSum (s : Finset ℕ) (p : ℕ → Prop) :
      (∑ i ∈ s, if p i then (1 : ℝ) else 0) =
      ((s.filter p).card : ℝ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        by_cases hi : p i <;> simp [hi, his, ih]
  have hcountReal (s : Finset ℝ≥0) (p : ℝ≥0 → Prop) :
      (∑ u ∈ s, if p u then (1 : ℝ) else 0) =
      ((s.filter p).card : ℝ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert u s hus ih =>
        by_cases hu : p u <;> simp [hu, hus, ih]
  have hgrid (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1),
        B.indicator (fun _ : ℝ => (1 : ℝ))
          (Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
           Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) =
      (((Finset.range (n + 1)).filter (fun i : ℕ =>
          Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card : ℝ) := by
    simpa [Set.indicator] using hcountSum (Finset.range (n + 1))
      (fun i : ℕ =>
        Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)
  have htrue :
      (∑ u ∈ S, B.indicator (fun _ : ℝ => (1 : ℝ))
        (Y u - Function.leftLim Y u)) =
      ((S.filter (fun u => Y u - Function.leftLim Y u ∈ B)).card : ℝ) := by
    simpa [Set.indicator] using hcountReal S
      (fun u => Y u - Function.leftLim Y u ∈ B)
  have hcast : Tendsto (fun n : ℕ =>
      (((Finset.range (n + 1)).filter (fun i : ℕ =>
        Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card : ℝ))
      atTop (𝓝 ((S.filter (fun u =>
        Y u - Function.leftLim Y u ∈ B)).card : ℝ)) := by
    simpa only [hgrid, htrue] using hlim
  exact ⟨S, hS,
    avram_p2_l_mesh_nat_count_stabilises_of_real_limit
      (fun n => ((Finset.range (n + 1)).filter (fun i : ℕ =>
        Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
        Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∈ B)).card)
      (S.filter (fun u => Y u - Function.leftLim Y u ∈ B)).card hcast⟩
