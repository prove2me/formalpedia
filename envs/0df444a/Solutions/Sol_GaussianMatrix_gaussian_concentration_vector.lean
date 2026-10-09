-- Prove2me | solution 1 for GaussianMatrix.gaussian_concentration_vector
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:25:46.08237+00:00
-- url     : https://prove2.me/submissions/6b385aa5-e951-4a85-882a-c538cdd3a91d

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_herbst_argument
import Theorems.Thm_GaussianMatrix_gaussian_lipschitz_entropy_bound

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.ConcVec

/-- `√(∑ xᵢ²) ≤ ∑ |xᵢ|`. -/
lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
  have h0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.sqrt_le_left h0]
  have : ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp [sq_abs]
  rw [this]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- A function that is `L`-Lipschitz for the Euclidean distance is continuous. -/
lemma continuous_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) : Continuous f := by
  have h : ∀ x y, dist (f x) (f y) ≤ (L * Fintype.card ι) * dist x y := by
    intro x y
    rw [Real.dist_eq]
    refine (hLip x y).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL
    refine (sqrt_sum_sq_le_sum_abs (fun i => x i - y i)).trans ?_
    calc ∑ i, |x i - y i| ≤ ∑ _i : ι, dist x y := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
      _ = Fintype.card ι * dist x y := by simp
  exact (LipschitzWith.of_dist_le' h).continuous

/-- `exp (a |y|)` is integrable for the standard Gaussian. -/
lemma integrable_exp_mul_abs_gaussianReal (a : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a * |y|)) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussianReal a).add
    (integrable_exp_mul_gaussianReal (-a))) (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-a * y)]
  · rw [abs_of_nonpos hy]
    have : a * -y = -a * y := by ring
    rw [this]; linarith [Real.exp_pos (a * y)]

/-- `exp (a ∑ |xᵢ|)` is integrable for the standard Gaussian product measure. -/
lemma integrable_exp_mul_sum_abs {ι : Type*} [Fintype ι] (a : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (a * ∑ i, |x i|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h := Integrable.fintype_prod (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun _ y => Real.exp (a * |y|)) (fun _ => integrable_exp_mul_abs_gaussianReal a)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.mul_sum, Real.exp_sum]

/-- Exponential integrability of Lipschitz functions under the standard Gaussian. -/
lemma integrable_exp_mul_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    Integrable (fun x => Real.exp (s * f x)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hc := continuous_of_lip f L hL hLip
  refine Integrable.mono' ((integrable_exp_mul_sum_abs (ι := ι) (|s| * L)).const_mul
    (Real.exp (|s| * |f 0|))) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have h1 : |f x| ≤ |f 0| + L * ∑ i, |x i| := by
    have := hLip x 0
    simp only [Pi.zero_apply, sub_zero] at this
    have h2 : Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := sqrt_sum_sq_le_sum_abs x
    have h3 : |f x| ≤ |f 0| + |f x - f 0| := by
      have := abs_sub_abs_le_abs_sub (f x) (f 0); linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL]
  have h4 : s * f x ≤ |s| * |f x| := by
    rw [← abs_mul]; exact le_abs_self _
  have h5 := mul_le_mul_of_nonneg_left h1 (abs_nonneg s)
  nlinarith

/-- Integrability of Lipschitz functions under the standard Gaussian. -/
lemma integrable_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hc := continuous_of_lip f L hL hLip
  refine Integrable.mono' ((integrable_exp_mul_of_lip f L hL hLip 1).add
    (integrable_exp_mul_of_lip f L hL hLip (-1))) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply]
  rcases le_total 0 (f x) with h | h
  · rw [abs_of_nonneg h]
    linarith [Real.add_one_le_exp (f x), Real.exp_pos (-f x)]
  · rw [abs_of_nonpos h]
    linarith [Real.add_one_le_exp (-f x), Real.exp_pos (f x)]

end GaussianMatrix.ConcVec

open GaussianMatrix

theorem solution {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hL : 0 < L) (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {x | (∫ y, f y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + L * t ≤ f x}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  open GaussianMatrix.ConcVec in
  refine ⟨integrable_of_lip f L hL.le hLip, ?_⟩
  set μ := Measure.pi fun _ : ι => gaussianReal 0 1 with hμ
  set E := ∫ y, f y ∂μ with hE
  have hint := integrable_exp_mul_of_lip f L hL.le hLip
  set l := t / L with hl
  have hl0 : 0 ≤ l := div_nonneg ht hL.le
  have hlL : l * L = t := by rw [hl]; field_simp
  have hherb := herbst_argument μ f (L ^ 2 / 2) hint (fun s _ => by
    have := gaussian_lipschitz_entropy_bound f L hLip s
    refine this.trans (le_of_eq ?_)
    ring) l hl0
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := f) (E + L * t) hl0 (hint l)
  have hmgf : mgf f μ l = ∫ ω, Real.exp (l * f ω) ∂μ := rfl
  rw [hmgf] at hch
  have hbound : μ.real {x | E + L * t ≤ f x} ≤ Real.exp (-t ^ 2 / 2) := by
    refine hch.trans ?_
    calc Real.exp (-l * (E + L * t)) * ∫ ω, Real.exp (l * f ω) ∂μ
        ≤ Real.exp (-l * (E + L * t)) * Real.exp (l * E + L ^ 2 / 2 * l ^ 2) :=
          mul_le_mul_of_nonneg_left hherb (Real.exp_pos _).le
      _ = Real.exp (-t ^ 2 / 2) := by
          rw [← Real.exp_add]; congr 1
          have : L * l = t := by rw [mul_comm]; exact hlL
          have h2 : L ^ 2 / 2 * l ^ 2 = t ^ 2 / 2 := by rw [← this]; ring
          rw [h2]
          have h3 : -l * (E + L * t) = -l * E - t * t := by rw [← this]; ring
          rw [h3]; ring
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hbound
