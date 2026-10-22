-- Prove2me | solution 1 for FiniteEnergyPlane.hofer_lemma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:45:25.736291+00:00
-- url     : https://prove2.me/submissions/38496be7-433a-4941-a2af-aca0afd05926

import Definitions.Def_FiniteEnergyPlane_Setting
open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

open Metric Filter Topology

theorem g69s_hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (g : X → ℝ)
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (x₀ : X) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ x : X, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε₀ * g x₀ ≤ ε * g x ∧ dist x x₀ ≤ 2 * ε₀ ∧
      ∀ y ∈ closedBall x ε, g y ≤ 2 * g x := by
  by_contra hcon
  push Not at hcon
  set e : ℕ → ℝ := fun k => ε₀ / 2 ^ k with he
  have he_pos : ∀ k, 0 < e k := fun k => by simp only [he]; positivity
  have he_le : ∀ k, e k ≤ ε₀ := fun k => by
    simp only [he]; exact div_le_self hε₀.le (one_le_pow₀ (by norm_num))
  have he_succ : ∀ k, e (k+1) = e k / 2 := fun k => by simp only [he]; rw [pow_succ]; ring
  let P : ℕ → X → Prop := fun k x => ε₀ * g x₀ ≤ e k * g x ∧ dist x x₀ ≤ 2 * ε₀ - 2 * e k
  have step : ∀ k x, P k x → ∃ y, dist y x ≤ e k ∧ 2 * g x < g y ∧ P (k+1) y := by
    intro k x hx
    obtain ⟨y, hy, hgy⟩ := hcon x (e k) (he_pos k) (he_le k) hx.1
      (by linarith [hx.2, he_pos k])
    rw [mem_closedBall] at hy
    refine ⟨y, hy, hgy, ?_, ?_⟩
    · rw [he_succ]
      have := hx.1
      have h2 : e k * g x ≤ e k / 2 * g y := by nlinarith [he_pos k]
      linarith
    · rw [he_succ]
      have := dist_triangle y x x₀
      linarith [hx.2]
  classical
  let next : ℕ → X → X := fun k x => if h : P k x then Classical.choose (step k x h) else x
  let seq : ℕ → X := fun k => Nat.rec x₀ (fun k y => next k y) k
  have seq_succ : ∀ k, seq (k+1) = next k (seq k) := fun k => rfl
  have hP : ∀ k, P k (seq k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [seq, he], ?_⟩
      show dist x₀ x₀ ≤ 2 * ε₀ - 2 * e 0
      simp [he]
    | succ k ih =>
      rw [seq_succ]
      simp only [next, dif_pos ih]
      exact (Classical.choose_spec (step k _ ih)).2.2
  have hstep : ∀ k, dist (seq (k+1)) (seq k) ≤ e k ∧ 2 * g (seq k) < g (seq (k+1)) := by
    intro k
    rw [seq_succ]
    simp only [next, dif_pos (hP k)]
    exact ⟨(Classical.choose_spec (step k _ (hP k))).1,
      (Classical.choose_spec (step k _ (hP k))).2.1⟩
  have hcau : CauchySeq seq := by
    refine cauchySeq_of_le_geometric_two (C := 2 * ε₀) (fun k => ?_)
    rw [dist_comm]
    have := (hstep k).1
    simp only [he] at this
    calc dist (seq (k+1)) (seq k) ≤ ε₀ / 2 ^ k := this
      _ = 2 * ε₀ / 2 / 2 ^ k := by ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have hgL : Tendsto (fun k => g (seq k)) atTop (𝓝 (g L)) := (hg.tendsto L).comp hL
  set c := g (seq 1)
  have hc : 0 < c := by
    have := (hstep 0).2
    have := hg0 (seq 0)
    show 0 < g (seq (0+1))
    linarith
  have hgrow : ∀ k, 2 ^ k * c ≤ g (seq (k+1)) := by
    intro k
    induction k with
    | zero => simp [c]
    | succ k ih =>
      have := (hstep (k+1)).2
      rw [pow_succ]
      nlinarith
  have htop : Tendsto (fun k => g (seq (k+1))) atTop atTop := by
    refine tendsto_atTop_mono hgrow ?_
    exact Tendsto.atTop_mul_const hc (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h2 : Tendsto (fun k => g (seq (k+1))) atTop (𝓝 (g L)) :=
    hgL.comp (tendsto_add_atTop_nat 1)
  exact not_tendsto_atTop_of_tendsto_nhds h2 htop

/-- Hofer's topological lemma: Wendl, Lemma 9.4 (p. 154); Hofer 1993, Lemma 26 (p. 535). Let
`X` be a complete metric space, `g : X → [0, ∞)` continuous, `x₀ ∈ X` and `ε₀ > 0`. There are
`x ∈ X` and `0 < ε ≤ ε₀` with `ε g(x) ≥ ε₀ g(x₀)`, `d(x, x₀) ≤ 2ε₀`, and `g(y) ≤ 2 g(x)` whenever
`d(y, x) ≤ ε`. (Wendl states the last property on the ball `B_ε(x)`; the closed ball is used
here.) -/
theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X] (g : X → ℝ)
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (x₀ : X) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ x : X, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε₀ * g x₀ ≤ ε * g x ∧ dist x x₀ ≤ 2 * ε₀ ∧
      ∀ y ∈ closedBall x ε, g y ≤ 2 * g x := by
  exact g69s_hofer g hg hg0 x₀ ε₀ hε₀

