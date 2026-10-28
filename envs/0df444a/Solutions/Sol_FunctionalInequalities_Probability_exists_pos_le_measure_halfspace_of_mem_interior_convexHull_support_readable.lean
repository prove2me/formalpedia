-- Prove2me | solution 1 for FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:16.654262+00:00
-- url     : https://prove2.me/submissions/5b89097b-3f1d-44dc-a485-56b7c631cc07

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Theorems.Thm_FunctionalInequalities_Probability_exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_readable
import Theorems.Thm_FunctionalInequalities_Probability_exists_pos_ball_inner_sub_pos_of_mem_support_readable

open MeasureTheory
open scoped RealInnerProductSpace
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteIndex
variable {α : Type*}
variable [DecidableEq α]
private lemma FunctionalInequalities.Probability.product_pos_of_pos
    (s : Finset α) (f : α → ℝ) (hf : ∀ a ∈ s, 0 < f a) :
    0 < ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_pos (hf a (Finset.mem_insert_self a s))
        (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
private lemma FunctionalInequalities.Probability.product_le_one_of_nonneg_of_le_one
    (s : Finset α) (f : α → ℝ)
    (h₀ : ∀ a ∈ s, 0 ≤ f a) (h₁ : ∀ a ∈ s, f a ≤ 1) :
    (∏ a ∈ s, f a) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hprod : 0 ≤ ∏ b ∈ s, f b := by
        exact Finset.prod_nonneg (fun b hb => h₀ b (Finset.mem_insert_of_mem hb))
      have hprod' : (∏ b ∈ s, f b) ≤ 1 := by
        apply ih
        · intro b hb
          exact h₀ b (Finset.mem_insert_of_mem hb)
        · intro b hb
          exact h₁ b (Finset.mem_insert_of_mem hb)
      have ha₀ : 0 ≤ f a := h₀ a (Finset.mem_insert_self a s)
      have ha₁ : f a ≤ 1 := h₁ a (Finset.mem_insert_self a s)
      calc
        f a * (∏ b ∈ s, f b) ≤ 1 * (∏ b ∈ s, f b) :=
          mul_le_mul_of_nonneg_right ha₁ hprod
        _ = ∏ b ∈ s, f b := one_mul _
        _ ≤ 1 := hprod'
private lemma FunctionalInequalities.Probability.product_le_factor_of_nonneg_of_le_one
    (s : Finset α) (f : α → ℝ) {a : α} (ha : a ∈ s)
    (h₀ : ∀ b ∈ s, 0 ≤ f b) (h₁ : ∀ b ∈ s, f b ≤ 1) :
    (∏ b ∈ s, f b) ≤ f a := by
  induction s using Finset.induction_on with
  | empty =>
      simp at ha
  | @insert b s hb ih =>
      rw [Finset.prod_insert hb]
      by_cases hba : a = b
      · subst a
        have hprod : 0 ≤ ∏ c ∈ s, f c := by
          exact Finset.prod_nonneg (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
        have hprod' : (∏ c ∈ s, f c) ≤ 1 := by
          exact product_le_one_of_nonneg_of_le_one s f
            (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
            (fun c hc => h₁ c (Finset.mem_insert_of_mem hc))
        have hb₀ : 0 ≤ f b := h₀ b (Finset.mem_insert_self b s)
        calc
          f b * (∏ c ∈ s, f c) ≤ f b * 1 :=
            mul_le_mul_of_nonneg_left hprod' hb₀
          _ = f b := mul_one _
      · have ha' : a ∈ s := by
          simpa [hba] using ha
        have hi :
            (∏ c ∈ s, f c) ≤ f a :=
          ih ha'
            (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
            (fun c hc => h₁ c (Finset.mem_insert_of_mem hc))
        have hprod : 0 ≤ ∏ c ∈ s, f c := by
          exact Finset.prod_nonneg (fun c hc => h₀ c (Finset.mem_insert_of_mem hc))
        have hb₁ : f b ≤ 1 := h₁ b (Finset.mem_insert_self b s)
        calc
          f b * (∏ c ∈ s, f c) ≤ 1 * (∏ c ∈ s, f c) :=
            mul_le_mul_of_nonneg_right hb₁ hprod
          _ = ∏ c ∈ s, f c := one_mul _
          _ ≤ f a := hi
end FiniteIndex
/-- Uniform positive mass of the strict open halfspaces through an interior point of the convex hull of the support. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E) {x₀ : E} (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ u : E, ‖u‖ = 1 → m ≤ ((μ : Measure E) {x | 0 < ⟪u, x - x₀⟫}).toReal := by
    classical
    let S := Metric.sphere (0 : E) 1
    have hchoice :
        ∀ u : S, ∃ y ∈ (μ : Measure E).support, ∃ δ > 0, ∃ r > 0,
          0 < (μ : Measure E) (Metric.ball y r) ∧
            ∀ v : E, ‖v - (u : E)‖ < δ →
              ∀ x ∈ Metric.ball y r, 0 < ⟪v, x - x₀⟫ := by
      intro u
      have hu : (u : E) ≠ 0 := by
        intro hzero
        have hu' := u.property
        rw [Metric.mem_sphere, hzero, dist_zero_right, norm_zero] at hu'
        norm_num at hu'
      obtain ⟨y, hy, hinner⟩ :=
        FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull_readable μ hx₀ hu
      obtain ⟨δ, hδ, r, hr, hm, hh⟩ :=
        FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support_readable μ hy hinner
      exact ⟨y, hy, δ, hδ, r, hr, hm, hh⟩
    choose y hy δ hδ r hr hmass hhalf using hchoice
    have hsub :
        ∀ u : S, IsOpen (Metric.ball (u : E) (δ u)) :=
      fun u => Metric.isOpen_ball
    have hcov :
        S ⊆ ⋃ u : S, Metric.ball (u : E) (δ u) := by
      intro u hu
      let v : S := ⟨u, hu⟩
      have hv : u ∈ Metric.ball (v : E) (δ v) := by
        rw [Metric.mem_ball, dist_self]
        exact hδ v
      exact Set.mem_iUnion.mpr ⟨v, hv⟩
    obtain ⟨t, ht⟩ :=
      (isCompact_sphere (0 : E) 1).elim_finite_subcover
        (fun u : S => Metric.ball (u : E) (δ u)) hsub hcov
    let f : S → ℝ :=
      fun u => ((μ : Measure E) (Metric.ball (y u) (r u))).toReal
    let m : ℝ := ∏ u ∈ t, f u
    have hfpos : ∀ u ∈ t, 0 < f u := by
      intro u hu
      dsimp [f]
      exact ENNReal.toReal_pos (ne_of_gt (hmass u))
        (measure_ne_top _ _)
    have hfnonneg : ∀ u ∈ t, 0 ≤ f u := by
      intro u hu
      exact le_of_lt (hfpos u hu)
    have hfleone : ∀ u ∈ t, f u ≤ 1 := by
      intro u hu
      dsimp [f]
      have hle :
          (μ : Measure E) (Metric.ball (y u) (r u)) ≤
            (μ : Measure E) Set.univ :=
        measure_mono (Set.subset_univ _)
      have hle' :
          ((μ : Measure E) (Metric.ball (y u) (r u))).toReal ≤
            ((μ : Measure E) Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hle
      simpa using hle'
    have hmpos : 0 < m := by
      dsimp [m]
      exact FunctionalInequalities.Probability.product_pos_of_pos t f hfpos
    have hmleone : m ≤ 1 := by
      dsimp [m]
      exact FunctionalInequalities.Probability.product_le_one_of_nonneg_of_le_one t f hfnonneg hfleone
    refine ⟨m, hmpos, hmleone, ?_⟩
    intro u hu
    have huS : u ∈ S := by
      change u ∈ Metric.sphere (0 : E) 1
      rw [Metric.mem_sphere, dist_zero_right]
      exact hu
    have hucover : u ∈ ⋃ v ∈ t, Metric.ball (v : E) (δ v) :=
      ht huS
    rcases Set.mem_iUnion.mp hucover with ⟨v, huv⟩
    rcases Set.mem_iUnion.mp huv with ⟨hv, huv⟩
    have huv' : ‖u - (v : E)‖ < δ v := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using huv
    have hmlefv : m ≤ f v := by
      dsimp [m]
      exact FunctionalInequalities.Probability.product_le_factor_of_nonneg_of_le_one t f hv
        hfnonneg hfleone
    have hball :
        Metric.ball (y v) (r v) ⊆
          {x : E | 0 < ⟪u, x - x₀⟫} := by
      intro x hx
      exact hhalf v u huv' x hx
    have hmeasure :
        (μ : Measure E) (Metric.ball (y v) (r v)) ≤
          (μ : Measure E) {x : E | 0 < ⟪u, x - x₀⟫} :=
      measure_mono hball
    have hreal :
        f v ≤ ((μ : Measure E) {x : E | 0 < ⟪u, x - x₀⟫}).toReal := by
      dsimp [f]
      exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
    exact hmlefv.trans hreal
