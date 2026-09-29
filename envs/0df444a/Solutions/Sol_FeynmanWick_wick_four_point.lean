-- Prove2me | solution 1 for FeynmanWick.wick_four_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:44:52.14136+00:00
-- url     : https://prove2.me/submissions/b79de1ec-5ee8-453d-9e27-e3cda1894c77

import Mathlib
import Definitions.Def_FeynmanWickPairings

/-! c07cdaf7 FeynmanWick.wick_four_point (Isserlis, four-point function of a centred Gaussian).
Route: for `e : Fin 4 → ℝ` the functional `L e = ∑ e i • proj (k i)` pushes `μ` forward to
`gaussianReal 0 v` (IsGaussian + centring), whose 2nd/4th moments are `v` and `3 v²` (iterated
derivatives of the mgf `exp (v t² / 2)`). Hence `E[(L e)^4] = 3 E[(L e)^2]^2`, and
`E[(L e)^2] = ∑ e i e j C i j`. Polarization over the 16 sign vectors `e ∈ {±1}^4`
(`384 x₀x₁x₂x₃ = ∑ (∏ e) (e·x)^4`) extracts the mixed moment. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace FeynmanWickC07

lemma deriv_cubic_gexp (v a b c e : ℝ) :
    deriv (fun t : ℝ => (a + b * t + c * t ^ 2 + e * t ^ 3) * Real.exp (v * t ^ 2 / 2))
      = fun t => ((b + 2 * c * t + 3 * e * t ^ 2)
          + (a + b * t + c * t ^ 2 + e * t ^ 3) * (v * t)) * Real.exp (v * t ^ 2 / 2) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => v * t ^ 2 / 2) (v * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul v).div_const 2
    exact this.congr_deriv (by ring)
  have hp : HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2 + e * t ^ 3)
      (b + 2 * c * t + 3 * e * t ^ 2) t := by
    have := (((hasDerivAt_const t a).fun_add ((hasDerivAt_id' t).const_mul b)).fun_add
      ((hasDerivAt_pow 2 t).const_mul c)).fun_add ((hasDerivAt_pow 3 t).const_mul e)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => (a + b * t + c * t ^ 2 + e * t ^ 3) * Real.exp (v * t ^ 2 / 2))
      ((b + 2 * c * t + 3 * e * t ^ 2) * Real.exp (v * t ^ 2 / 2)
        + (a + b * t + c * t ^ 2 + e * t ^ 3) * (Real.exp (v * t ^ 2 / 2) * (v * t))) t :=
    hp.mul h1.exp
  rw [h2.deriv]; ring

lemma gauss_moments (v : NNReal) :
    ∫ y, y ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) ∧
    ∫ y, y ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  set w : ℝ := (v : ℝ) with hw
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 v)
      = fun t : ℝ => (1 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3) * Real.exp (w * t ^ 2 / 2) := by
    rw [mgf_fun_id_gaussianReal]; funext t; simp [hw]
  have d1 := deriv_cubic_gexp w 1 0 0 0
  have e1 : (fun t : ℝ => ((0 + 2 * 0 * t + 3 * 0 * t ^ 2) + (1 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3) * (w * t))
      * Real.exp (w * t ^ 2 / 2)) = fun t => (0 + w * t + 0 * t ^ 2 + 0 * t ^ 3) * Real.exp (w * t ^ 2 / 2) := by
    funext t; ring
  have d2 := deriv_cubic_gexp w 0 w 0 0
  have e2 : (fun t : ℝ => ((w + 2 * 0 * t + 3 * 0 * t ^ 2) + (0 + w * t + 0 * t ^ 2 + 0 * t ^ 3) * (w * t))
      * Real.exp (w * t ^ 2 / 2)) = fun t => (w + 0 * t + w ^ 2 * t ^ 2 + 0 * t ^ 3) * Real.exp (w * t ^ 2 / 2) := by
    funext t; ring
  have d3 := deriv_cubic_gexp w w 0 (w ^ 2) 0
  have e3 : (fun t : ℝ => ((0 + 2 * w ^ 2 * t + 3 * 0 * t ^ 2) + (w + 0 * t + w ^ 2 * t ^ 2 + 0 * t ^ 3) * (w * t))
      * Real.exp (w * t ^ 2 / 2)) = fun t => (0 + 3 * w ^ 2 * t + 0 * t ^ 2 + w ^ 3 * t ^ 3) * Real.exp (w * t ^ 2 / 2) := by
    funext t; ring
  have d4 := deriv_cubic_gexp w 0 (3 * w ^ 2) 0 (w ^ 3)
  have h0 : (0:ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v)) := by simp
  have m2 := iteratedDeriv_mgf_zero h0 2
  have m4 := iteratedDeriv_mgf_zero h0 4
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, hmgf, d1, e1, d2, e2] at m2
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
    iteratedDeriv_zero, hmgf, d1, e1, d2, e2, d3, e3, d4] at m4
  simp only [Pi.pow_apply] at m2 m4
  constructor
  · rw [← m2]; simp
  · rw [← m4]; simp


lemma wick4_aux {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin 4 → Fin d) :
    ∫ x, x (k 0) * x (k 1) * x (k 2) * x (k 3) ∂μ
      = (∫ x, x (k 0) * x (k 1) ∂μ) * (∫ x, x (k 2) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 2) ∂μ) * (∫ x, x (k 1) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 3) ∂μ) * (∫ x, x (k 1) * x (k 2) ∂μ) := by
  classical
  have hmem : ∀ (j : Fin d) (p : ENNReal), p ≠ ⊤ →
      MemLp (fun x : EuclideanSpace ℝ (Fin d) => x j) p μ := by
    intro j p hp
    exact IsGaussian.memLp_dual μ (EuclideanSpace.proj j) p hp
  have hint1 : ∀ j : Fin d, Integrable (fun x : EuclideanSpace ℝ (Fin d) => x j) μ := by
    intro j
    exact memLp_one_iff_integrable.1 (hmem j 1 (by simp))
  have hij : ∀ i j : Fin 4,
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => x (k i) * x (k j)) μ := by
    intro i j
    exact (hmem (k i) 2 (by simp)).integrable_mul (hmem (k j) 2 (by simp))
  let L : (Fin 4 → ℝ) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)) :=
    fun e => ∑ i, e i • (EuclideanSpace.proj (k i) : StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
  have hL : ∀ (e : Fin 4 → ℝ) (x : EuclideanSpace ℝ (Fin d)), L e x = ∑ i, e i * x (k i) := by
    intro e x; simp [L]
  have hint4 : ∀ e : Fin 4 → ℝ, Integrable (fun x => (L e x) ^ 4) μ := by
    intro e
    have h := (IsGaussian.memLp_dual μ (L e) ((4 : ℕ) : ENNReal) (by simp)).integrable_norm_pow
      (by norm_num)
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, rfl⟩ _
  have h2 : ∀ e : Fin 4 → ℝ, ∫ x, (L e x) ^ 2 ∂μ
      = ∑ i, ∑ j, e i * e j * ∫ x, x (k i) * x (k j) ∂μ := by
    intro e
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
        (L e x) ^ 2 = ∑ i, ∑ j, e i * e j * (x (k i) * x (k j)) := by
      intro x; rw [hL]; simp only [Fin.sum_univ_four]; ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hij i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hij i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have h4 : ∀ e : Fin 4 → ℝ, ∫ x, (L e x) ^ 4 ∂μ = 3 * (∫ x, (L e x) ^ 2 ∂μ) ^ 2 := by
    intro e
    have hm := IsGaussian.map_eq_gaussianReal (μ := μ) (L e)
    have hmean : ∫ x, L e x ∂μ = 0 := by
      simp_rw [hL]
      rw [integral_finsetSum _ (fun i _ => (hint1 (k i)).const_mul _)]
      simp [integral_const_mul, hcent]
    rw [hmean] at hm
    obtain ⟨g2, g4⟩ := gauss_moments (Var[L e; μ]).toNNReal
    have i4 : ∫ x, (L e x) ^ 4 ∂μ = ∫ y, y ^ 4 ∂(μ.map (L e)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    have i2 : ∫ x, (L e x) ^ 2 ∂μ = ∫ y, y ^ 2 ∂(μ.map (L e)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    rw [i4, i2, hm, g2, g4]
  let sg : Bool → ℝ := fun b => if b then 1 else -1
  let E : Bool × Bool × Bool × Bool → Fin 4 → ℝ :=
    fun b => ![sg b.1, sg b.2.1, sg b.2.2.1, sg b.2.2.2]
  let w : Bool × Bool × Bool × Bool → ℝ := fun b => sg b.1 * sg b.2.1 * sg b.2.2.1 * sg b.2.2.2
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d), x (k 0) * x (k 1) * x (k 2) * x (k 3)
      = (1 / 384) * ∑ b, w b * (L (E b) x) ^ 4 := by
    intro x
    simp only [hL, Fin.sum_univ_four, Fintype.sum_prod_type, Fintype.sum_bool, E, w, sg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Bool.false_eq_true, ↓reduceIte]
    ring
  have hsym : ∀ i j : Fin 4, ∫ x, x (k i) * x (k j) ∂μ = ∫ x, x (k j) * x (k i) ∂μ := by
    intro i j; exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  calc ∫ x, x (k 0) * x (k 1) * x (k 2) * x (k 3) ∂μ
      = ∫ x, (1 / 384) * ∑ b, w b * (L (E b) x) ^ 4 ∂μ := integral_congr_ae (ae_of_all _ hpt)
    _ = (1 / 384) * ∑ b, w b * (3 * (∑ i, ∑ j, E b i * E b j * ∫ x, x (k i) * x (k j) ∂μ) ^ 2) := by
      rw [integral_const_mul, integral_finsetSum _ (fun b _ => (hint4 (E b)).const_mul (w b))]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul, h4, h2]
    _ = _ := by
      simp only [Fin.sum_univ_four, Fintype.sum_prod_type, Fintype.sum_bool, E, w, sg,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Bool.false_eq_true, ↓reduceIte]
      rw [hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2]
      ring

end FeynmanWickC07

open MeasureTheory ProbabilityTheory in
theorem solution {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin 4 → Fin d) :
    ∫ x, x (k 0) * x (k 1) * x (k 2) * x (k 3) ∂μ
      = (∫ x, x (k 0) * x (k 1) ∂μ) * (∫ x, x (k 2) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 2) ∂μ) * (∫ x, x (k 1) * x (k 3) ∂μ)
        + (∫ x, x (k 0) * x (k 3) ∂μ) * (∫ x, x (k 1) * x (k 2) ∂μ) := by
  exact FeynmanWickC07.wick4_aux μ hcent k
