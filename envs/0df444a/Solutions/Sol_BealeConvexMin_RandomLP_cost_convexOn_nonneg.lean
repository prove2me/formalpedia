-- Prove2me | solution 1 for BealeConvexMin.RandomLP.cost_convexOn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:27:44.756329+00:00
-- url     : https://prove2.me/submissions/9c7b2d45-a55d-4f1d-b65c-cb4aea5eee09

import Definitions.Def_BealeConvexMin_RandomLP_expectedCost
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic
open Matrix MeasureTheory Set
open BealeConvexMin.RandomLP

private theorem attained_spec {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ)
    (f : Fin p → ℝ) (b : Fin m → ℝ) (h : SecondStageAttained D f b) :
    ∃ y∈feasY D b,secondStageValue D f b=dotProduct f y ∧
      ∀ z∈feasY D b,secondStageValue D f b≤dotProduct f z := by
  obtain ⟨y,hy,hmin⟩ := h
  have hi : IsLeast ((fun z => dotProduct f z) '' feasY D b) (dotProduct f y) := by
    refine ⟨⟨y,hy,rfl⟩,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hmin z hz
  have he : secondStageValue D f b=dotProduct f y := hi.csInf_eq
  exact ⟨y,hy,he,fun z hz => he.symm ▸ hmin z hz⟩

private theorem value_le {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ)
    (f : Fin p → ℝ) (b : Fin m → ℝ) (h : SecondStageAttained D f b)
    (y : Fin p → ℝ) (hy : y∈feasY D b) : secondStageValue D f b≤dotProduct f y := by
  obtain ⟨z,hz,he,hmin⟩ := attained_spec D f b h
  exact hmin y hy

private theorem value_convex {m p : ℕ} (D : Matrix (Fin m) (Fin p) ℝ)
    (f : Fin p → ℝ) (t s : Fin m → ℝ) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (ht : SecondStageAttained D f t) (hs : SecondStageAttained D f s)
    (hm : SecondStageAttained D f (a • t+b • s)) :
    secondStageValue D f (a • t+b • s)≤a*secondStageValue D f t+b*secondStageValue D f s := by
  obtain ⟨y,hy,hey,hmy⟩ := attained_spec D f t ht
  obtain ⟨z,hz,hez,hmz⟩ := attained_spec D f s hs
  have hh := value_le D f (a • t+b • s) hm (a • y+b • z) (by
    refine ⟨fun j => add_nonneg (mul_nonneg ha (hy.1 j)) (mul_nonneg hb (hz.1 j)),?_⟩
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hy.2,hz.2])
  simpa only [hey,hez,dotProduct_add,dotProduct_smul,smul_eq_mul] using hh

theorem solution {m n p : ℕ} (c : Fin n → ℝ) (f : Fin p → ℝ)
    (D : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (β : Fin m → ℝ)
    (hatt : ∀ x : Fin n → ℝ, 0 ≤ x → SecondStageAttained D f (β - A *ᵥ x)) :
    ConvexOn ℝ {x : Fin n → ℝ | 0 ≤ x} (cost c f D A β) := by
  have hc : Convex ℝ {x : Fin n → ℝ | 0≤x} := by
    intro x hx y hy a b ha hb hab j
    exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
  refine ⟨hc,?_⟩
  intro x hx y hy a b ha hb hab
  have he : β-A *ᵥ (a • x+b • y)=a • (β-A *ᵥ x)+b • (β-A *ᵥ y) := by
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul]
    ext i
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    nlinarith only [congrArg (fun r : ℝ => r*β i) hab]
  have hm := hatt _ (hc hx hy ha hb hab)
  rw [he] at hm
  have hh := value_convex D f (β-A *ᵥ x) (β-A *ᵥ y) a b ha hb (hatt x hx) (hatt y hy) hm
  change cost c f D A β (a • x+b • y)≤a*cost c f D A β x+b*cost c f D A β y
  unfold cost
  rw [he,dotProduct_add,dotProduct_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  nlinarith only [hh]
