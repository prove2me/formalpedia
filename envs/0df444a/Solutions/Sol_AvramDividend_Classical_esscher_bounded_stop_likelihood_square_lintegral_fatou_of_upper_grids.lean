-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_likelihood_square_lintegral_fatou_of_upper_grids
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:44:42.336075+00:00
-- url     : https://prove2.me/submissions/77d20021-cddf-4b93-a547-7894200168c2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AV_99d9

theorem measurable_of_grid {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (f : Ω → ℝ≥0) (grid : Finset ℝ≥0) (hgrid : ∀ ω, f ω ∈ grid)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | f ω = s}) : Measurable f := by
  classical
  intro S _
  have : f ⁻¹' S = ⋃ s ∈ grid.filter (· ∈ S), {ω : Ω | f ω = s} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter,
      exists_prop]
    exact ⟨fun h => ⟨f ω, ⟨hgrid ω, h⟩, rfl⟩, fun ⟨s, ⟨_, hs⟩, e⟩ => e ▸ hs⟩
  rw [this]
  exact Finset.measurableSet_biUnion _ fun s hs =>
    𝓕.le s _ (hstop s (Finset.mem_filter.1 hs).1)

end AV_99d9

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n → s ≤ T)
    (hstop : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    (∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)) ^ 2) ∂P) ≤
      ENNReal.ofReal
        (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2) with hf
  have hconv := AvramDividend.Classical.esscher_stopped_likelihood_tendsto_of_right_approximation
    X θ hθ τ τn hlim habove
  have hlimf : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (ENNReal.ofReal
      ((Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) ^ 2))) := by
    intro ω
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hconv ω).pow 2)
  have hjoint := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hmeas : ∀ n, AEMeasurable (f n) P := by
    intro n
    have hτn : Measurable (τn n) := AV_99d9.measurable_of_grid (𝓕 := 𝓕) (τn n) (grid n)
      (hgrid n) (hstop n)
    have hXn : Measurable fun ω => X.X (τn n ω) ω :=
      hjoint.comp (hτn.prodMk measurable_id)
    have hτr : Measurable fun ω => ((τn n ω : ℝ≥0) : ℝ) := measurable_coe_nnreal_real.comp hτn
    exact (ENNReal.measurable_ofReal.comp
      (((measurable_const.mul hXn).sub (hτr.mul measurable_const)).exp.pow_const 2)).aemeasurable
  have hbd : ∀ n, ∫⁻ ω, f n ω ∂P ≤
      ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|)) := by
    intro n
    have hL := AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_lintegral_bound
      X θ hθ T H (τn n) (grid n) (hgrid n) (hT n) (hstop n) (hbound n)
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hL
    simp only [hf]
    congr 1
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) ^ 2) ∂P)
      = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P :=
        lintegral_congr fun ω => ((hlimf ω).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hmeas
    _ ≤ _ := Filter.liminf_le_of_frequently_le' (Frequently.of_forall hbd)
