-- Prove2me | solution 1 for EmpiricalBernstein.SVP.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:44:21.103972+00:00
-- url     : https://prove2.me/submissions/abcfe706-7732-409c-9e5f-a377efb72f21

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_swap

set_option autoImplicit false

open MeasureTheory EmpiricalBernstein.SVP

lemma ebs13_mp {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → Bool) :
    MeasurePreserving
      (fun p : (Fin n → 𝒳) × (Fin n → 𝒳) =>
        (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  have he := measurePreserving_arrowProdEquivProdArrow 𝒳 𝒳 (Fin n) (fun _ => μ) (fun _ => μ)
  have hφ : MeasurePreserving (fun (a : Fin n → 𝒳 × 𝒳) i => if σ i then a i else (a i).swap)
      (Measure.pi fun _ => μ.prod μ) (Measure.pi fun _ => μ.prod μ) := by
    refine measurePreserving_pi (fun _ => μ.prod μ) (fun _ => μ.prod μ)
      (f := fun i (q : 𝒳 × 𝒳) => if σ i then q else q.swap) (fun i => ?_)
    by_cases h : σ i
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h]; simpa using Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hc := he.comp (hφ.comp (MeasurePreserving.symm _ he))
  have heq : (fun p : (Fin n → 𝒳) × (Fin n → 𝒳) =>
        (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2))
      = (MeasurableEquiv.arrowProdEquivProdArrow 𝒳 𝒳 (Fin n)) ∘
        ((fun (a : Fin n → 𝒳 × 𝒳) i => if σ i then a i else (a i).swap) ∘
          (MeasurableEquiv.arrowProdEquivProdArrow 𝒳 𝒳 (Fin n)).symm) := by
    funext p
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · by_cases h : σ i <;>
        simp [swap, h, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases h : σ i <;>
        simp [swap, h, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  rw [heq]
  exact hc

theorem solution {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    {n : ℕ} (G : (Fin n → 𝒳) × (Fin n → 𝒳) → ℝ) (hGm : Measurable G)
    (hG : ∀ p, G p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p, G p ∂((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ≤ ⨆ p : (Fin n → 𝒳) × (Fin n → 𝒳),
          ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            G (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2) := by
  set Q := (Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ) with hQ
  set T : (Fin n → Bool) → (Fin n → 𝒳) × (Fin n → 𝒳) → (Fin n → 𝒳) × (Fin n → 𝒳) :=
    fun σ p => (swap σ p.1 p.2, swap (fun i => !σ i) p.1 p.2) with hT
  have hmp : ∀ σ, MeasurePreserving (T σ) Q Q := fun σ => ebs13_mp μ σ
  have hint : ∀ σ, ∫ p, G (T σ p) ∂Q = ∫ p, G p ∂Q := by
    intro σ
    calc ∫ p, G (T σ p) ∂Q = ∫ p, G p ∂(Measure.map (T σ) Q) :=
          (integral_map (hmp σ).measurable.aemeasurable hGm.aestronglyMeasurable).symm
      _ = ∫ p, G p ∂Q := by rw [(hmp σ).map_eq]
  have hGT : ∀ σ, Integrable (fun p => G (T σ p)) Q := fun σ =>
    Integrable.of_bound (hGm.comp (hmp σ).measurable).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        have := hG (T σ p)
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]
        exact this.2)
  have hmeas : Measurable (fun p => ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p)) :=
    (Finset.measurable_sum _ (fun σ _ => hGm.comp (hmp σ).measurable)).const_mul _
  have hle : ∀ p, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p) ≤ 1 := by
    intro p
    have h1 : ∑ σ : Fin n → Bool, G (T σ p) ≤ (2 : ℝ) ^ n := by
      calc ∑ σ : Fin n → Bool, G (T σ p) ≤ ∑ σ : Fin n → Bool, (1 : ℝ) :=
            Finset.sum_le_sum (fun σ _ => (hG _).2)
        _ = (2 : ℝ) ^ n := by simp
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    calc ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p)
        ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n := by gcongr
      _ = 1 := inv_mul_cancel₀ h2.ne'
  have hnn : ∀ p, 0 ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p) := fun p =>
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun σ _ => (hG _).1))
  have hAint : Integrable (fun p => ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p)) Q :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn p)]
        exact hle p)
  have hsum : ∫ p, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p) ∂Q = ∫ p, G p ∂Q := by
    rw [integral_const_mul, integral_finset_sum _ (fun σ _ => hGT σ)]
    simp only [hint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hc : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by simp
    rw [hc]
    field_simp
  have hbdd : BddAbove (Set.range fun p => ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p)) :=
    ⟨1, by rintro _ ⟨p, rfl⟩; exact hle p⟩
  rw [← hsum]
  calc ∫ p, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ p) ∂Q
      ≤ ∫ p, (⨆ q, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ q)) ∂Q :=
        integral_mono hAint (integrable_const _) (fun p => le_ciSup hbdd p)
    _ = ⨆ q, ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, G (T σ q) := by
        simp
