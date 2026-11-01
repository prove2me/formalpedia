-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_discounted_actual_right_payment_atoms_finite_grid_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:57:51.465396+00:00
-- url     : https://prove2.me/submissions/2f8c4569-74af-4a4c-8fd8-9dbde68e3f4a

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

/-- Finite sets of actual discounted chronological right-payment atoms
converge uniformly over all sufficiently large finite supersets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    let f : A → ℝ := fun s =>
      Real.exp (-(q * (s : ℝ))) *
        (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)
    ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset A, ∀ G : Finset A, F ⊆ G →
        |(∑ s ∈ G, f s) - (∑' s : A, f s)| < ε := by
  dsimp only
  let A : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
  let δ : A → ℝ := fun s =>
    rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω
  let f : A → ℝ := fun s => Real.exp (-(q * (s : ℝ))) * δ s
  have hδ : Summable δ :=
    (avram_wave4_04b_full_right_payment_jump_support_summable
      D hD ω T).2
  have hf : Summable f := by
    apply Summable.of_norm_bounded hδ
    intro s
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.property.1
    have hδ0 : 0 ≤ δ s := le_of_lt s.property.2.2
    have hE0 : 0 ≤ Real.exp (-(q * (s : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hE1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hqtime : 0 ≤ q * (s : ℝ) := mul_nonneg hq hs0
      linarith
    calc
      ‖f s‖ = Real.exp (-(q * (s : ℝ))) * δ s := by
        simp only [f, Real.norm_eq_abs, abs_mul, abs_of_nonneg hE0,
          abs_of_nonneg hδ0]
      _ ≤ 1 * δ s := mul_le_mul_of_nonneg_right hE1 hδ0
      _ = δ s := one_mul _
  have hTendsto : Filter.Tendsto
      (fun G : Finset A => ∑ s ∈ G, f s) Filter.atTop
      (𝓝 (∑' s : A, f s)) := hf.hasSum
  intro ε hε
  have hEvent : ∀ᶠ G : Finset A in Filter.atTop,
      (∑ s ∈ G, f s) ∈ Metric.ball (∑' s : A, f s) ε :=
    hTendsto (Metric.ball_mem_nhds (∑' s : A, f s) hε)
  obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp hEvent
  refine ⟨F, ?_⟩
  intro G hFG
  have h := hF G hFG
  simpa only [Metric.mem_ball, Real.dist_eq] using h
