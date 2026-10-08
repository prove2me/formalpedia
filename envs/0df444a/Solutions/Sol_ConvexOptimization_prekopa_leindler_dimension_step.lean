-- Prove2me | solution 1 for ConvexOptimization.prekopa_leindler_dimension_step
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T16:27:59.095591+00:00
-- url     : https://prove2.me/submissions/a6105746-9575-475f-bd66-b12a94777ed3

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace PrekopaLeindlerDimensionStepAux

def PLAt (α : Type*) [MeasurableSpace α] [Add α] [SMul ℝ α]
    (μ : Measure α) (l : ℝ) : Prop :=
  ∀ (f g h : α → ℝ≥0∞), Measurable f → Measurable g → Measurable h →
    (∀ x y : α, f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - l) * (∫⁻ x, g x ∂μ) ^ l ≤ ∫⁻ x, h x ∂μ

theorem PLAt.prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Add α] [Add β] [SMul ℝ α] [SMul ℝ β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {l : ℝ} (hα : PLAt α μ l) (hβ : PLAt β ν l) :
    PLAt (α × β) (μ.prod ν) l := by
  intro f g h hf hg hh hple
  let F : α → ℝ≥0∞ := fun x => ∫⁻ y, f (x, y) ∂ν
  let G : α → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂ν
  let H : α → ℝ≥0∞ := fun x => ∫⁻ y, h (x, y) ∂ν
  have hFm : Measurable F := by
    exact Measurable.lintegral_prod_right
      (ν := ν) (f := fun x y => f (x, y)) (by exact hf)
  have hGm : Measurable G := by
    exact Measurable.lintegral_prod_right
      (ν := ν) (f := fun x y => g (x, y)) (by exact hg)
  have hHm : Measurable H := by
    exact Measurable.lintegral_prod_right
      (ν := ν) (f := fun x y => h (x, y)) (by exact hh)
  have hFGH : ∀ x₁ x₂ : α,
      F x₁ ^ (1 - l) * G x₂ ^ l ≤ H ((1 - l) • x₁ + l • x₂) := by
    intro x₁ x₂
    apply hβ (fun y => f (x₁, y)) (fun y => g (x₂, y))
      (fun y => h ((1 - l) • x₁ + l • x₂, y))
    · exact hf.comp measurable_prodMk_left
    · exact hg.comp measurable_prodMk_left
    · exact hh.comp measurable_prodMk_left
    · intro y₁ y₂
      simpa using hple (x₁, y₁) (x₂, y₂)
  have hout := hα F G H hFm hGm hHm hFGH
  rw [lintegral_prod f hf.aemeasurable,
      lintegral_prod g hg.aemeasurable,
      lintegral_prod h hh.aemeasurable]
  exact hout

theorem PLAt.linearEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [AddCommMonoid α] [AddCommMonoid β] [Module ℝ α] [Module ℝ β]
    (μ : Measure α) (ν : Measure β) {l : ℝ}
    (e : α ≃ₗ[ℝ] β) (he' : Measurable e.symm)
    (hmp : MeasurePreserving e μ ν) (hβ : PLAt β ν l) :
    PLAt α μ l := by
  intro f g h hf hg hh hple
  have hF : Measurable (fun b => f (e.symm b)) := hf.comp he'
  have hG : Measurable (fun b => g (e.symm b)) := hg.comp he'
  have hH : Measurable (fun b => h (e.symm b)) := hh.comp he'
  have hres := hβ
    (fun b => f (e.symm b))
    (fun b => g (e.symm b))
    (fun b => h (e.symm b))
    hF hG hH (by
      intro x y
      simpa using hple (e.symm x) (e.symm y))
  have int_f : (∫⁻ b, f (e.symm b) ∂ν) = ∫⁻ a, f a ∂μ := by
    calc
      _ = ∫⁻ a, f (e.symm (e a)) ∂μ := (hmp.lintegral_comp hF).symm
      _ = _ := by simp
  have int_g : (∫⁻ b, g (e.symm b) ∂ν) = ∫⁻ a, g a ∂μ := by
    calc
      _ = ∫⁻ a, g (e.symm (e a)) ∂μ := (hmp.lintegral_comp hG).symm
      _ = _ := by simp
  have int_h : (∫⁻ b, h (e.symm b) ∂ν) = ∫⁻ a, h a ∂μ := by
    calc
      _ = ∫⁻ a, h (e.symm (e a)) ∂μ := (hmp.lintegral_comp hH).symm
      _ = _ := by simp
  rwa [int_f, int_g, int_h] at hres

noncomputable def finSuccLinearEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toEquiv := (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0).symm
  map_add' f g := by ext <;> rfl
  map_smul' c f := by ext <;> rfl

end PrekopaLeindlerDimensionStepAux

open PrekopaLeindlerDimensionStepAux

theorem solution {n : ℕ}
    (h_one :
      ∀ (l : ℝ) (_hl0 : 0 < l) (_hl1 : l < 1)
        (f g h : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞),
        Measurable f → Measurable g → Measurable h →
        (∀ x y : EuclideanSpace ℝ (Fin 1),
          f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x)
    (h_n :
      ∀ (l : ℝ) (_hl0 : 0 < l) (_hl1 : l < 1)
        (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
        Measurable f → Measurable g → Measurable h →
        (∀ x y : EuclideanSpace ℝ (Fin n),
          f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
        (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin (n + 1)),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by
  have h1 := h_one l hl0 hl1
  have hn := h_n l hl0 hl1
  change PLAt (EuclideanSpace ℝ (Fin 1)) volume l at h1
  change PLAt (EuclideanSpace ℝ (Fin n)) volume l at hn

  have h1Raw : PLAt (Fin 1 → ℝ) volume l :=
    PLAt.linearEquiv volume volume
      (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
      (WithLp.measurable_ofLp 2 (Fin 1 → ℝ))
      (PiLp.volume_preserving_toLp (Fin 1)) h1

  have hR : PLAt ℝ volume l := by
    apply PLAt.linearEquiv volume volume
      (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
    · exact (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
    · exact (volume_preserving_funUnique (Fin 1) ℝ).symm
        (MeasurableEquiv.funUnique (Fin 1) ℝ)
    · exact h1Raw

  have hnRaw : PLAt (Fin n → ℝ) volume l :=
    PLAt.linearEquiv volume volume
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
      (WithLp.measurable_ofLp 2 (Fin n → ℝ))
      (PiLp.volume_preserving_toLp (Fin n)) hn

  have hprod : PLAt (ℝ × (Fin n → ℝ)) volume l := by
    exact PLAt.prod volume volume hR hnRaw

  have hRawSucc : PLAt (Fin (n + 1) → ℝ) volume l := by
    apply PLAt.linearEquiv volume volume (finSuccLinearEquiv n)
    · exact (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable
    · exact (volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0)
    · exact hprod

  have hsucc : PLAt (EuclideanSpace ℝ (Fin (n + 1))) volume l :=
    PLAt.linearEquiv volume volume
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ))
      (WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ))
      (PiLp.volume_preserving_ofLp (Fin (n + 1))) hRawSucc

  exact hsucc f g h hf hg hh hple
