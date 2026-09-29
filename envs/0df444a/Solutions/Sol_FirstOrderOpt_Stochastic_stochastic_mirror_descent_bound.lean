-- Prove2me | solution 1 for FirstOrderOpt.Stochastic.stochastic_mirror_descent_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:59:32.346105+00:00
-- url     : https://prove2.me/submissions/b70d7f7c-97b5-43cf-9a7b-4812f2ddff49

import Mathlib

namespace FirstOrderOpt.Stochastic

open MeasureTheory

/-- A nonnegative function on `ℝ` vanishing everywhere except at `1/2`, where it equals `100`. -/
noncomputable def aux_smdb_f (y : ℝ) : ℝ := if y = 1 / 2 then 100 else 0

theorem aux_smdb_f_nonneg (y : ℝ) : 0 ≤ aux_smdb_f y := by
  unfold aux_smdb_f; split_ifs <;> norm_num

/-- The iterates: `x 1 = 1`, all others `0`. -/
noncomputable def aux_smdb_x (t : ℕ) : ℝ := if t = 1 then 1 else 0

theorem aux_smdb_f_x (t : ℕ) : aux_smdb_f (aux_smdb_x t) = 0 := by
  unfold aux_smdb_f aux_smdb_x
  split_ifs with h1 h2 h2 <;> norm_num at *

end FirstOrderOpt.Stochastic

open FirstOrderOpt.Stochastic MeasureTheory

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (M σ : ℝ) (hM : 0 < M) (hσ : 0 < σ)
    (x : ℕ → Ω → E) (G : ℕ → Ω → E →L[ℝ] ℝ) (g : E → E →L[ℝ] ℝ) (γ : ℕ → ℝ)
    (hx : ∀ t ω, x t ω ∈ X) (hγ : ∀ t, 0 < γ t)
    (hsub : ∀ t ω, ∀ y ∈ X, f (x t ω) + (g (x t ω)) (y - x t ω) ≤ f y)
    (hgnorm : ∀ t ω, ‖g (x t ω)‖ ≤ M)
    (hintsecmom : ∀ t, Integrable (fun ω => ‖G t ω - g (x t ω)‖ ^ 2) μ)
    (hsecmom : ∀ t, ∫ ω, ‖G t ω - g (x t ω)‖ ^ 2 ∂μ ≤ σ ^ 2)
    (hmin : ∀ t ω, ∀ y ∈ X, γ t * (G t ω) (x (t + 1) ω) + V (x t ω) (x (t + 1) ω) ≤
      γ t * (G t ω) y + V (x t ω) y)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y)
    (hintcross : ∀ t, Integrable (fun ω => γ t * (G t ω - g (x t ω)) (x t ω - xstar)) μ)
    (hcross : ∀ t, ∫ ω, γ t * (G t ω - g (x t ω)) (x t ω - xstar) ∂μ = 0)
    (s k : ℕ) (hsk : s ≤ k)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω = (∑ t ∈ Finset.Icc s k, γ t)⁻¹ • ∑ t ∈ Finset.Icc s k, γ t • x t ω)
    (hintf : Integrable (fun ω => f (xbar ω)) μ)
    (hintV : Integrable (fun ω => V (x s ω) xstar) μ),
    ∫ ω, f (xbar ω) ∂μ - f xstar ≤ (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (∫ ω, V (x s ω) xstar ∂μ + (M ^ 2 + σ ^ 2) * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2)) := by
  intro H
  -- Counterexample: `Ω = Unit` with the Dirac measure, `E = ℝ`, `X = univ`, `V = 0`,
  -- `G = 0`, `g = 0`, `γ = 1`, `M = σ = 1`, `x 1 = 1` and `x t = 0` otherwise, `s = 0`, `k = 1`,
  -- `x* = 0`, and `f = 100 · 𝟙_{1/2}`. Then `x̄ = 1/2` and the bound reads `100 ≤ 2`.
  have key := H (E := ℝ) (Ω := Unit) (μ := Measure.dirac ()) Set.univ aux_smdb_f
    (fun _ _ => 0) 1 1 one_pos one_pos (fun t _ => aux_smdb_x t) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 1) (fun _ _ => Set.mem_univ _) (fun _ => one_pos)
    (fun t _ y _ => by simp [aux_smdb_f_x, aux_smdb_f_nonneg])
    (fun _ _ => by simp)
    (fun _ => by simp)
    (fun _ => by simp)
    (fun _ _ _ _ => by simp)
    0 (Set.mem_univ _) (fun y _ => by
      have h0 : aux_smdb_f 0 = 0 := by simp [aux_smdb_f]
      rw [h0]; exact aux_smdb_f_nonneg y)
    (fun _ => by simp)
    (fun _ => by simp)
    0 1 zero_le_one
    (fun _ => (1 / 2 : ℝ)) ?hxbar (integrable_const _) (integrable_const _)
  · have h12 : aux_smdb_f (1 / 2) = 100 := by simp [aux_smdb_f]
    have h0 : aux_smdb_f 0 = 0 := by simp [aux_smdb_f]
    simp only [h12, h0] at key
    norm_num at key
  case hxbar =>
    intro _
    simp [aux_smdb_x]
