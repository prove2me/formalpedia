-- Prove2me | solution 1 for BealeConvexMin.RandomLP.discrete_expected_cost_lp
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:27:46.291988+00:00
-- url     : https://prove2.me/submissions/a60f8c62-2576-4d61-afec-9d013933ca4e

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

theorem solution {R : Type*} [Fintype R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (P : Measure R) [IsProbabilityMeasure P] {m n p : ℕ}
    (c : Fin n → ℝ) (f : Fin p → ℝ) (D : Matrix (Fin m) (Fin p) ℝ)
    (A : R → Matrix (Fin m) (Fin n) ℝ) (β : R → Fin m → ℝ) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (hatt : ∀ r, SecondStageAttained D f (β r - A r *ᵥ x)) :
    IsLeast {z : ℝ | ∃ y : R → Fin p → ℝ,
        (∀ r, 0 ≤ y r ∧ A r *ᵥ x + D *ᵥ y r = β r) ∧
          z = c ⬝ᵥ x + ∑ r, (P {r}).toReal * (f ⬝ᵥ y r)}
      (expectedCost P c f D A β x) := by
  classical
  have hp : (∑ r,(P {r}).toReal)=1 := by
    have hh := sum_measureReal_singleton (μ := P) (Finset.univ : Finset R)
    simpa [Measure.real] using hh
  have he : expectedCost P c f D A β x=dotProduct c x+
      ∑ r,(P {r}).toReal*secondStageValue D f (β r-A r *ᵥ x) := by
    unfold expectedCost
    rw [integral_fintype (Integrable.of_finite)]
    simp only [cost,smul_eq_mul,Measure.real,mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,hp,one_mul]
  have hs (r : R) := attained_spec D f (β r-A r *ᵥ x) (hatt r)
  choose y hy hey hmin using hs
  constructor
  · refine ⟨y,?_,?_⟩
    · intro r
      exact ⟨(hy r).1,by rw [(hy r).2]; abel⟩
    · simpa only [hey] using he
  · rintro z ⟨w,hw,rfl⟩
    rw [he]
    apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro r hr
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply hmin r
    exact ⟨(hw r).1,by have hh := (hw r).2; exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hh)⟩
