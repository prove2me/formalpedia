-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_of_forall_eventually_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:21:41.227139+00:00
-- url     : https://prove2.me/submissions/9e3e25bc-2d9d-45be-8c9a-64132fdf4db0

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Metric Filter Topology

namespace FiniteEnergyPlane

/-- If for every `δ > 0` the relation `P k` eventually has a solution in `B(x₀, δ) × B(y₀, δ)`, then
there are sequences `x k → x₀`, `y k → y₀` with `P k (x k) (y k)` for all large `k`. -/
theorem exists_tendsto_of_forall_eventually_exists_aux {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (P : ℕ → X → Y → Prop) (x₀ : X) (y₀ : Y)
    (h : ∀ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ x ∈ ball x₀ δ, ∃ y ∈ ball y₀ δ, P k x y) :
    ∃ (x : ℕ → X) (y : ℕ → Y), Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      ∀ᶠ k in atTop, P k (x k) (y k) := by
  classical
  set A : ℕ → Set ℝ := fun k => {δ | 0 < δ ∧ ∃ x ∈ ball x₀ δ, ∃ y ∈ ball y₀ δ, P k x y} with hA
  have hbdd : ∀ k, BddBelow (A k) := fun k => ⟨0, fun δ hδ => hδ.1.le⟩
  have hch : ∀ k, ∃ p : X × Y, (A k).Nonempty → P k p.1 p.2 ∧
      dist p.1 x₀ < sInf (A k) + 1 / ((k : ℝ) + 1) ∧
      dist p.2 y₀ < sInf (A k) + 1 / ((k : ℝ) + 1) := by
    intro k
    by_cases hne : (A k).Nonempty
    · have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨δ, hδ, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (sInf (A k)) hpos)
      obtain ⟨-, x, hx, y, hy, hP⟩ := hδ
      exact ⟨(x, y), fun _ => ⟨hP, (mem_ball.1 hx).trans hlt, (mem_ball.1 hy).trans hlt⟩⟩
    · exact ⟨(x₀, y₀), fun h => absurd h hne⟩
  choose p hp using hch
  have hsmall : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have key : ∀ ε > (0 : ℝ), ∀ᶠ k in atTop, (A k).Nonempty ∧
      sInf (A k) + 1 / ((k : ℝ) + 1) < ε := by
    intro ε hε
    have h1 := h (ε / 2) (half_pos hε)
    have h2 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε / 2 :=
      hsmall.eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [h1, h2] with k hk1 hk2
    have hmem : ε / 2 ∈ A k := ⟨half_pos hε, hk1⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    have := csInf_le (hbdd k) hmem
    linarith
  refine ⟨fun k => (p k).1, fun k => (p k).2, ?_, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [key ε hε] with k hk
    exact ((hp k hk.1).2.1).trans hk.2
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [key ε hε] with k hk
    exact ((hp k hk.1).2.2).trans hk.2
  · filter_upwards [key 1 one_pos] with k hk
    exact (hp k hk.1).1

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology

theorem solution {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (P : ℕ → X → Y → Prop) (x₀ : X) (y₀ : Y)
    (h : ∀ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ x ∈ ball x₀ δ, ∃ y ∈ ball y₀ δ, P k x y) :
    ∃ (x : ℕ → X) (y : ℕ → Y), Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      ∀ᶠ k in atTop, P k (x k) (y k) :=
  FiniteEnergyPlane.exists_tendsto_of_forall_eventually_exists_aux P x₀ y₀ h
