-- Prove2me | solution 1 for BealeConvexMin.RandomLP.expected_cost_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T04:28:27.864486+00:00
-- url     : https://prove2.me/submissions/1a9e3a14-20eb-4501-b126-06ca1875cb27

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
import Definitions.Def_BealeConvexMin_RandomLP_expectedCost

open Matrix MeasureTheory BealeConvexMin.RandomLP in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (A : Ω → Matrix (Fin m) (Fin n) ℝ) (β : Ω → Fin m → ℝ)
    (hatt : ∀ x : Fin n → ℝ, 0 ≤ x → ∀ᵐ ω ∂P, SecondStageAttained D f (β ω - A ω *ᵥ x))
    (hint : ∀ x : Fin n → ℝ, 0 ≤ x → Integrable (fun ω => cost c f D (A ω) (β ω) x) P) :
    ConvexOn ℝ {x : Fin n → ℝ | 0 ≤ x} (expectedCost P c f D A β) := by
  -- value equals the attained minimum
  have hval : ∀ b : Fin m → ℝ, SecondStageAttained D f b →
      ∃ y ∈ feasY D b, secondStageValue D f b = f ⬝ᵥ y ∧
        ∀ y' ∈ feasY D b, f ⬝ᵥ y ≤ f ⬝ᵥ y' := by
    intro b hb
    obtain ⟨y, hy, hmin⟩ := hb
    refine ⟨y, hy, ?_, hmin⟩
    have hl : IsLeast ((fun y => f ⬝ᵥ y) '' feasY D b) (f ⬝ᵥ y) := by
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rintro _ ⟨y', hy', rfl⟩
      exact hmin y' hy'
    exact hl.csInf_eq
  -- convexity of the second-stage value along a segment
  have hconv : ∀ (b1 b2 : Fin m → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b →
      SecondStageAttained D f b1 → SecondStageAttained D f b2 →
      SecondStageAttained D f (a • b1 + b • b2) →
      secondStageValue D f (a • b1 + b • b2) ≤
        a * secondStageValue D f b1 + b * secondStageValue D f b2 := by
    intro b1 b2 a b ha hb h1 h2 h3
    obtain ⟨y1, hy1, hv1, -⟩ := hval b1 h1
    obtain ⟨y2, hy2, hv2, -⟩ := hval b2 h2
    obtain ⟨y3, hy3, hv3, hmin3⟩ := hval _ h3
    have hfeas : a • y1 + b • y2 ∈ feasY D (a • b1 + b • b2) := by
      refine ⟨add_nonneg (smul_nonneg ha hy1.1) (smul_nonneg hb hy2.1), ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hy1.2, hy2.2]
    rw [hv1, hv2, hv3]
    calc f ⬝ᵥ y3 ≤ f ⬝ᵥ (a • y1 + b • y2) := hmin3 _ hfeas
      _ = a * f ⬝ᵥ y1 + b * f ⬝ᵥ y2 := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · exact convex_Ici (0 : Fin n → ℝ)
  intro x1 hx1 x2 hx2 a b ha hb hab
  have hx1' : (0 : Fin n → ℝ) ≤ x1 := hx1
  have hx2' : (0 : Fin n → ℝ) ≤ x2 := hx2
  have hx3 : (0 : Fin n → ℝ) ≤ a • x1 + b • x2 :=
    add_nonneg (smul_nonneg ha hx1') (smul_nonneg hb hx2')
  have hrhs : ∀ ω, β ω - A ω *ᵥ (a • x1 + b • x2) =
      a • (β ω - A ω *ᵥ x1) + b • (β ω - A ω *ᵥ x2) := by
    intro ω
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(β ω i)) * hab
  have hpt : ∀ᵐ ω ∂P, cost c f D (A ω) (β ω) (a • x1 + b • x2) ≤
      a * cost c f D (A ω) (β ω) x1 + b * cost c f D (A ω) (β ω) x2 := by
    filter_upwards [hatt x1 hx1', hatt x2 hx2', hatt _ hx3] with ω h1 h2 h3
    rw [hrhs ω] at h3
    have hc := hconv _ _ a b ha hb h1 h2 h3
    unfold cost
    rw [hrhs ω, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [hc]
  show expectedCost P c f D A β (a • x1 + b • x2) ≤
    a * expectedCost P c f D A β x1 + b * expectedCost P c f D A β x2
  unfold expectedCost
  have hi1 := (hint x1 hx1').const_mul a
  have hi2 := (hint x2 hx2').const_mul b
  calc ∫ ω, cost c f D (A ω) (β ω) (a • x1 + b • x2) ∂P
      ≤ ∫ ω, (a * cost c f D (A ω) (β ω) x1 + b * cost c f D (A ω) (β ω) x2) ∂P :=
        integral_mono_ae (hint _ hx3) (hi1.add hi2) hpt
    _ = a * ∫ ω, cost c f D (A ω) (β ω) x1 ∂P + b * ∫ ω, cost c f D (A ω) (β ω) x2 ∂P := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
