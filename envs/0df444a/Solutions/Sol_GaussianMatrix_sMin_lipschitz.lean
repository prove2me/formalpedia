-- Prove2me | solution 1 for GaussianMatrix.sMin_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:31:52.444164+00:00
-- url     : https://prove2.me/submissions/6f0a2ffb-fad7-490b-ae7a-f7ee2b88103c

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Row-wise Cauchy–Schwarz: `‖B x‖₂² ≤ ‖B‖_F² ‖x‖₂²`. -/
lemma sMinLip_mulVec_dot_le {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  unfold frobSq
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) x
  calc (∑ j, B i j * x j) * (∑ j, B i j * x j) = (∑ j, B i j * x j) ^ 2 := by ring
    _ ≤ (∑ j, B i j ^ 2) * ∑ j, x j ^ 2 := h
    _ = (∑ j, B i j ^ 2) * ∑ j, x j * x j := by simp only [sq]

lemma sMinLip_frobSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (B : Matrix m n ℝ) :
    0 ≤ frobSq B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sMinLip_sqrt_dot_eq_norm {m : Type*} [Fintype m] (v : m → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ m)‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- Triangle inequality for the Euclidean length `√(v ⬝ᵥ v)`. -/
lemma sMinLip_sqrt_dot_add_le {m : Type*} [Fintype m] (u v : m → ℝ) :
    Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  rw [sMinLip_sqrt_dot_eq_norm, sMinLip_sqrt_dot_eq_norm, sMinLip_sqrt_dot_eq_norm,
    WithLp.toLp_add]
  exact norm_add_le _ _

/-- One half of the Lipschitz bound: `σ_min(A) ≤ σ_min(B) + ‖A - B‖_F`. -/
lemma sMin_le_sMin_add_frobNorm {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : sMin A ≤ sMin B + frobNorm (A - B) := by
  have hF : 0 ≤ frobNorm (A - B) := Real.sqrt_nonneg _
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · unfold sMin
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
    linarith
  · rw [← sub_le_iff_le_add]
    unfold sMin
    refine le_ciInf fun x => ?_
    have hbdd : BddBelow (Set.range fun y : {x : n → ℝ // x ⬝ᵥ x = 1} =>
        Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact Real.sqrt_nonneg _
    have h1 := ciInf_le hbdd x
    have h2 : Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) ≤ Real.sqrt ((B *ᵥ x.1) ⬝ᵥ (B *ᵥ x.1)) +
        Real.sqrt (((A - B) *ᵥ x.1) ⬝ᵥ ((A - B) *ᵥ x.1)) := by
      have hsplit : A *ᵥ x.1 = B *ᵥ x.1 + (A - B) *ᵥ x.1 := by
        rw [Matrix.sub_mulVec]; abel
      rw [hsplit]
      exact sMinLip_sqrt_dot_add_le _ _
    have h3 : Real.sqrt (((A - B) *ᵥ x.1) ⬝ᵥ ((A - B) *ᵥ x.1)) ≤ frobNorm (A - B) := by
      have := sMinLip_mulVec_dot_le (A - B) x.1
      rw [x.2, mul_one] at this
      exact Real.sqrt_le_sqrt this
    linarith

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (A B : Matrix (Fin N) (Fin n) ℝ) :
    |sMin A - sMin B| ≤ frobNorm (A - B) := by
  rw [abs_le]
  have h1 := sMin_le_sMin_add_frobNorm A B
  have h2 := sMin_le_sMin_add_frobNorm B A
  have h3 : frobNorm (B - A) = frobNorm (A - B) := by
    unfold frobNorm frobSq
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]
    ring
  constructor <;> linarith
