-- Prove2me | solution 1 for ChenStein.OneVar.telescoping_term_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:08:46.892025+00:00
-- url     : https://prove2.me/submissions/ce7ef954-b769-4975-8cd5-7e03ad0a2449

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting



namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma p_nonneg' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {I : Type*}
    (X : I → Ω → ℕ) (α : I) : 0 ≤ p P X α := by
  unfold p; exact measureReal_nonneg

lemma integral_X_eq_p {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {I : Type*}
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1) (γ : I) :
    ∫ ω, (X γ ω : ℝ) ∂P = p P X γ := by
  have : (fun ω => (X γ ω : ℝ)) = Set.indicator {ω | X γ ω = 1} 1 := by
    ext ω
    by_cases h1 : X γ ω = 1
    · simp [Set.indicator, h1]
    · have h0 : X γ ω = 0 := by have := hX01 γ ω; omega
      simp [Set.indicator, h0]
  have hms : MeasurableSet {ω | X γ ω = 1} := (hXm γ) (measurableSet_singleton 1)
  rw [this, integral_indicator_one hms]
  rfl

lemma measurable_castX {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (γ : I) :
    Measurable (fun ω => (X γ ω : ℝ)) :=
  measurable_from_nat.comp (hXm γ)

theorem telescoping_term_le_core {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1) (α β : I)
    (U : Ω → ℕ) (hUm : Measurable U) (f : ℕ → ℝ) (D : ℝ)
    (hD : ∀ w, |Δ f w| ≤ D) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω)) ∂P
      ≤ D * (pab P X α β + p P X α * p P X β) := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0)
  have hpa := p_nonneg' P X α
  have hpb := p_nonneg' P X β
  have hpab : 0 ≤ pab P X α β := by
    unfold pab; exact integral_nonneg (fun ω => by positivity)
  have hpt : ∀ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω))
      ≤ D * ((X α ω : ℝ) * X β ω + p P X α * X β ω) := by
    intro ω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hX01 β ω) with h0 | h1
    · simp [h0]
    · rw [h1]
      simp only [Nat.cast_one, mul_one]
      have hXa : (0 : ℝ) ≤ X α ω := by positivity
      have h2 : |f (U ω + 1) - f (U ω)| ≤ D := hD (U ω)
      have h3 : |(X α ω : ℝ) - p P X α| ≤ (X α ω : ℝ) + p P X α := by
        calc |(X α ω : ℝ) - p P X α| ≤ |(X α ω : ℝ)| + |p P X α| := abs_sub _ _
          _ = (X α ω : ℝ) + p P X α := by rw [abs_of_nonneg hXa, abs_of_nonneg hpa]
      calc ((X α ω : ℝ) - p P X α) * (f (U ω + 1) - f (U ω))
          ≤ |((X α ω : ℝ) - p P X α) * (f (U ω + 1) - f (U ω))| := le_abs_self _
        _ = |(X α ω : ℝ) - p P X α| * |f (U ω + 1) - f (U ω)| := abs_mul _ _
        _ ≤ ((X α ω : ℝ) + p P X α) * D :=
            mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
        _ = D * ((X α ω : ℝ) + p P X α) := by ring
  have hmA : Measurable (fun ω => (X α ω : ℝ) * X β ω) :=
    (measurable_castX X hXm α).mul (measurable_castX X hXm β)
  have hmB : Measurable (fun ω => p P X α * (X β ω : ℝ)) :=
    (measurable_castX X hXm β).const_mul _
  have hiA : Integrable (fun ω => (X α ω : ℝ) * X β ω) P := by
    refine Integrable.of_bound hmA.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ha : (X α ω : ℝ) ≤ 1 := by exact_mod_cast hX01 α ω
    have hb : (X β ω : ℝ) ≤ 1 := by exact_mod_cast hX01 β ω
    have : (0:ℝ) ≤ X α ω := by positivity
    have : (0:ℝ) ≤ X β ω := by positivity
    nlinarith
  have hiB : Integrable (fun ω => p P X α * (X β ω : ℝ)) P := by
    refine Integrable.of_bound hmB.aestronglyMeasurable (p P X α) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : (X β ω : ℝ) ≤ 1 := by exact_mod_cast hX01 β ω
    nlinarith
  have hR : ∫ ω, D * ((X α ω : ℝ) * X β ω + p P X α * X β ω) ∂P
      = D * (pab P X α β + p P X α * p P X β) := by
    rw [integral_const_mul, integral_add hiA hiB, integral_const_mul,
      integral_X_eq_p P X hXm hX01 β]
    rfl
  by_cases hint : Integrable
      (fun ω => ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω))) P
  · rw [← hR]
    exact integral_mono hint ((hiA.add hiB).const_mul _) (fun ω => hpt ω)
  · rw [integral_undef hint]
    positivity

end ChenStein.OneVar

open ChenStein.OneVar
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1) (α β : I)
    (U : Ω → ℕ) (hUm : Measurable U) (f : ℕ → ℝ) (D : ℝ)
    (hD : ∀ w, |Δ f w| ≤ D) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω)) ∂P
      ≤ D * (pab P X α β + p P X α * p P X β) := by
  exact telescoping_term_le_core P X hXm hX01 α β U hUm f D hD
