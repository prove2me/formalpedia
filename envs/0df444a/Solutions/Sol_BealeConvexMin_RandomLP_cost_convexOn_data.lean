-- Prove2me | solution 1 for BealeConvexMin.RandomLP.cost_convexOn_data
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:27:45.575998+00:00
-- url     : https://prove2.me/submissions/b74cef0d-68db-473a-b12a-922c99b1028f

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
    (D : Matrix (Fin m) (Fin p) ℝ) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (K : Set (Matrix (Fin m) (Fin n) ℝ × (Fin m → ℝ))) (hK : Convex ℝ K)
    (hatt : ∀ q ∈ K, SecondStageAttained D f (q.2 - q.1 *ᵥ x)) :
    ConvexOn ℝ K (fun q => cost c f D q.1 q.2 x) := by
  refine ⟨hK,?_⟩
  intro q hq r hr a b ha hb hab
  have he : (a • q+b • r).2-(a • q+b • r).1 *ᵥ x=a • (q.2-q.1 *ᵥ x)+b • (r.2-r.1 *ᵥ x) := by
    change (a • q.2+b • r.2)-(a • q.1+b • r.1) *ᵥ x=_
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec]
    module
  have hm := hatt _ (hK hq hr ha hb hab)
  rw [he] at hm
  have hh := value_convex D f (q.2-q.1 *ᵥ x) (r.2-r.1 *ᵥ x) a b ha hb (hatt q hq) (hatt r hr) hm
  change cost c f D (a • q+b • r).1 (a • q+b • r).2 x≤a*cost c f D q.1 q.2 x+b*cost c f D r.1 r.2 x
  unfold cost
  rw [he]
  have hc := congrArg (fun z : ℝ => z*dotProduct c x) hab
  nlinarith only [hh,hc]
