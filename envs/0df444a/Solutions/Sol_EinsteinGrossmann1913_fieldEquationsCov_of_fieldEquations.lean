-- Prove2me | solution 1 for EinsteinGrossmann1913.fieldEquationsCov_of_fieldEquations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:22:38.345213+00:00
-- url     : https://prove2.me/submissions/ac03f608-e068-4c23-b526-9a264a73d57d

import Definitions.Def_EinsteinGrossmann1913_Defs

open EinsteinGrossmann1913
open scoped Matrix

private lemma smooth_det (g : Field2) (hg : IsMetricField g) :
    ContDiff ℝ 2 (fun x => (g x).det) := by
  classical
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => hg.contDiff (σ i) i)

private lemma smooth_gamma (g : Field2) (hg : IsMetricField g) (a b : Fin 4) :
    ContDiff ℝ 2 (fun x => gamma g x a b) := by
  classical
  have hadj : ContDiff ℝ 2 (fun x => (g x).adjugate a b) := by
    simp only [Matrix.adjugate_apply]
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro i _
    by_cases h : σ i = b
    · simp only [Matrix.updateRow_apply, h, if_true]
      exact contDiff_const
    · simpa only [Matrix.updateRow_apply, h, if_false] using hg.contDiff (σ i) i
  have hdet := (smooth_det g hg).inv (fun x => ne_of_lt (hg.det_neg x))
  have he : (fun x => gamma g x a b) =
      (fun x => (g x).det⁻¹ * (g x).adjugate a b) := by
    funext x
    simp [gamma, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply]
  rw [he]
  exact hdet.mul hadj

private lemma smooth_density (g : Field2) (hg : IsMetricField g) :
    ContDiff ℝ 2 (sqrtNegDet g) := by
  exact (smooth_det g hg).neg.sqrt (fun x => neg_ne_zero.mpr (ne_of_lt (hg.det_neg x)))

private lemma metric_symm (g : Field2) (hg : IsMetricField g) (x : Coord) :
    (g x)ᵀ = g x := by
  ext i j
  exact hg.symm x j i

private lemma inverse_mul (g : Field2) (hg : IsMetricField g) (x : Coord) :
    gamma g x * g x = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_lt (hg.det_neg x)))

private lemma mul_inverse (g : Field2) (hg : IsMetricField g) (x : Coord) :
    g x * gamma g x = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_lt (hg.det_neg x)))

private lemma inverse_symm (g : Field2) (hg : IsMetricField g) (x : Coord) :
    (gamma g x)ᵀ = gamma g x := by
  simp only [gamma, Matrix.transpose_nonsing_inv, metric_symm g hg x]

private lemma lower_matrix (g Θ : Field2) (x : Coord) :
    lowerIndices g Θ x = g x * Θ x * (g x)ᵀ := by
  ext i j
  simp only [lowerIndices, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private noncomputable def md (a : Fin 4) (F : Field2) : Field2 :=
  fun x i j => pd a (fun y => F y i j) x

private lemma md_mul (a : Fin 4) (F G : Field2) (x : Coord)
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    md a (fun y => F y * G y) x = md a F x * G x + F x * md a G x := by
  classical
  ext i j
  simp only [md, pd, Matrix.mul_apply]
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => F y i k * G y k j) (fun k _ => (hF i k).mul (hG k j))]
  simp only [sum_apply, Matrix.add_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [md, pd]
  rw [fderiv_fun_mul (c := fun y => F y i k) (d := fun y => G y k j) (hF i k) (hG k j)]
  simp [smul_eq_mul, mul_comm, add_comm]

private lemma differentiated_inverse (g : Field2) (hg : IsMetricField g)
    (x : Coord) (a : Fin 4) :
    g x * md a (gamma g) x * g x = -md a g x := by
  have hgd (i j : Fin 4) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.contDiff i j).differentiable (by norm_num) x
  have hhd (i j : Fin 4) : DifferentiableAt ℝ (fun y => gamma g y i j) x :=
    (smooth_gamma g hg i j).differentiable (by norm_num) x
  have he : md a (fun y => gamma g y * g y) x = 0 := by
    have he : (fun y => gamma g y * g y) = fun _ => (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
      funext (inverse_mul g hg)
    rw [he]
    ext i j
    simp [md, pd]
  rw [md_mul _ _ _ _ hhd hgd] at he
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => g x * M) he
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, mul_inverse g hg x,
    Matrix.one_mul, Matrix.mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma smooth_pd (f : Coord → ℝ) (hf : ContDiff ℝ 2 f) (a : Fin 4) :
    ContDiff ℝ 1 (fun x => pd a f x) := by
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

private lemma md_neg (a : Fin 4) (F : Field2) (x : Coord) :
    md a (fun y => -F y) x = -md a F x := by
  ext i j
  simp [md, pd]

private lemma md_symm (a : Fin 4) (F : Field2)
    (hF : ∀ x, (F x)ᵀ = F x) (x : Coord) : (md a F x)ᵀ = md a F x := by
  ext i j
  change pd a (fun y => F y j i) x = pd a (fun y => F y i j) x
  congr 1
  funext y
  exact congrFun (congrFun (hF y) i) j

private lemma inverse_deriv (g : Field2) (hg : IsMetricField g) (x : Coord) (a : Fin 4) :
    md a (gamma g) x = - (gamma g x * md a g x * gamma g x) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => gamma g x * M * gamma g x)
    (differentiated_inverse g hg x a)
  simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, inverse_mul g hg x,
    Matrix.one_mul] at h
  simpa only [Matrix.mul_assoc, mul_inverse g hg x, Matrix.mul_one] using h

private lemma weighted_second_inverse (g : Field2) (hg : IsMetricField g)
    (a b : Fin 4) (f : Coord → ℝ) (hf : ContDiff ℝ 1 f) (x : Coord) :
    g x * md a (fun y => f y • md b (gamma g) y) x * g x =
      -md a (fun y => f y • md b g y) x +
      f x • (md a g x * gamma g x * md b g x + md b g x * gamma g x * md a g x) := by
  have hgd (i j : Fin 4) := (hg.contDiff i j).differentiable (by norm_num) x
  have hbd (i j : Fin 4) := (smooth_pd _ (smooth_gamma g hg i j) b).differentiable (by norm_num) x
  have hfd := hf.differentiable (by norm_num) x
  have hpd (i j : Fin 4) : DifferentiableAt ℝ
      (fun y => (f y • md b (gamma g) y) i j) x := hfd.mul (hbd i j)
  have hprod (i j : Fin 4) : DifferentiableAt ℝ
      (fun y => (g y * (f y • md b (gamma g) y)) i j) x := by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (hgd i k).mul (hpd k j)
  have he : (fun y => g y * (f y • md b (gamma g) y) * g y) =
      fun y => -(f y • md b g y) := by
    funext y
    rw [Matrix.mul_smul, Matrix.smul_mul, differentiated_inverse g hg y b, smul_neg]
  have hd := congrArg (fun F : Field2 => md a F x) he
  rw [md_mul _ _ _ _ hprod hgd, md_mul _ _ _ _ hgd hpd, md_neg] at hd
  rw [inverse_deriv g hg x b] at hd
  simp only [Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg,
    Matrix.neg_mul, smul_neg, ← Matrix.mul_assoc, mul_inverse g hg x, Matrix.one_mul] at hd
  simp only [Matrix.mul_assoc, inverse_mul g hg x, Matrix.mul_one] at hd
  ext i j
  have hi := congrFun (congrFun hd i) j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
    smul_add] at hi ⊢
  simp only [Matrix.mul_assoc] at hi ⊢
  linarith

private noncomputable def quadratic (g : Field2) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => ∑ i, ∑ j, md a g x i j * md b (gamma g) x i j

private lemma stress_matrix (κ : ℝ) (g : Field2) (hg : IsMetricField g) (x : Coord) :
    gravStressEnergy κ g x = -(1 / (2 * κ)) •
      (gamma g x * quadratic g x * gamma g x -
        (1 / 2 * ∑ a, ∑ b, gamma g x a b * quadratic g x a b) • gamma g x) := by
  classical
  ext i j
  simp only [gravStressEnergy, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply]
  congr 1
  simp only [Finset.sum_sub_distrib]
  congr 1
  · simp only [Matrix.mul_apply, quadratic, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro r _
    have hs := congrFun (congrFun (inverse_symm g hg x) b) i
    simp only [Matrix.transpose_apply] at hs
    rw [hs]
    dsimp [md]
    ring
  · simp only [quadratic, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro r _
    dsimp [md]
    ring

private lemma stress_cov_matrix (κ : ℝ) (g : Field2) (x : Coord) :
    gravStressEnergyCov κ g x = -(1 / (2 * κ)) •
      (quadratic g x -
        (1 / 2 * ∑ a, ∑ b, gamma g x a b * quadratic g x a b) • g x) := by
  ext i j
  simp only [gravStressEnergyCov, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, quadratic, md]
  congr 1
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  ring

private lemma lower_stress (κ : ℝ) (g : Field2) (hg : IsMetricField g) (x : Coord) :
    lowerIndices g (gravStressEnergy κ g) x = gravStressEnergyCov κ g x := by
  rw [lower_matrix, metric_symm g hg x, stress_matrix κ g hg x,
    stress_cov_matrix κ g x]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, mul_inverse g hg x, Matrix.one_mul]
  simp only [Matrix.mul_assoc, inverse_mul g hg x, Matrix.mul_one]

private noncomputable def laplace (g F : Field2) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / sqrtNegDet g x) • ∑ a : Fin 4, ∑ b : Fin 4,
    md a (fun y => (gamma g y a b * sqrtNegDet g y) • md b F y) x

private noncomputable def energy (g F V : Field2) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, gamma g x a b • (md a F x * V x * md b F x)

private lemma matrix_contraction (A V B : Matrix (Fin 4) (Fin 4) ℝ) (hB : Bᵀ = B)
    (i j : Fin 4) :
    (∑ t : Fin 4, ∑ r : Fin 4, V t r * A i t * B j r) = (A * V * B) i j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  have hb := congrFun (congrFun hB t) j
  simp only [Matrix.transpose_apply] at hb
  rw [hb]
  ring

private lemma operator_matrix (g : Field2) (hg : IsMetricField g) (x : Coord) :
    entwurfDelta g x = laplace g (gamma g) x - energy g (gamma g) g x ∧
    entwurfD g x = laplace g g x - energy g g (gamma g) x := by
  constructor
  all_goals
    ext i j
    simp only [entwurfDelta, entwurfD, Matrix.of_apply, Matrix.sub_apply,
      laplace, energy, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    congr 1
  · simp only [md, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [← matrix_contraction _ _ _ (md_symm b _ (inverse_symm g hg) x) i j]
    simp only [md, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro r _
    ring
  · simp only [md, Matrix.smul_apply, Finset.mul_sum, smul_eq_mul]
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [← matrix_contraction _ _ _ (md_symm b _ (metric_symm g hg) x) i j]
    simp only [md, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro r _
    ring

private lemma lower_energy (g : Field2) (hg : IsMetricField g) (x : Coord) :
    g x * energy g (gamma g) g x * g x = energy g g (gamma g) x := by
  unfold energy
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [inverse_deriv g hg x a, inverse_deriv g hg x b]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, mul_inverse g hg x, Matrix.one_mul]
  simp only [Matrix.mul_assoc, inverse_mul g hg x, Matrix.mul_one]

private lemma lower_laplace (g : Field2) (hg : IsMetricField g) (x : Coord) :
    g x * laplace g (gamma g) x * g x =
      -laplace g g x + (2 : ℝ) • energy g g (gamma g) x := by
  have hS : sqrtNegDet g x ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hg.det_neg x)))
  unfold laplace
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  have he (a b : Fin 4) := weighted_second_inverse g hg a b
    (fun y => gamma g y a b * sqrtNegDet g y)
    (((smooth_gamma g hg a b).of_le (by norm_num)).mul
      ((smooth_density g hg).of_le (by norm_num))) x
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_neg_distrib, smul_add, smul_neg]
  congr 1
  have hs : (∑ a : Fin 4, ∑ b : Fin 4,
      (gamma g x a b * sqrtNegDet g x) • (md b g x * gamma g x * md a g x)) =
      ∑ a : Fin 4, ∑ b : Fin 4,
      (gamma g x a b * sqrtNegDet g x) • (md a g x * gamma g x * md b g x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h := congrFun (congrFun (inverse_symm g hg x) a) b
    simp only [Matrix.transpose_apply] at h
    rw [h]
  simp only [Finset.sum_add_distrib]
  rw [hs, ← two_smul ℝ]
  unfold energy
  simp only [smul_smul, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  field_simp [hS]

private lemma lower_operator (g : Field2) (hg : IsMetricField g) (x : Coord) :
    lowerIndices g (entwurfDelta g) x = -entwurfD g x := by
  rw [lower_matrix, metric_symm g hg x, (operator_matrix g hg x).1,
    (operator_matrix g hg x).2, Matrix.mul_sub, Matrix.sub_mul,
    lower_energy g hg x, lower_laplace g hg x]
  module

theorem solution (κ : ℝ) (_hκ : κ ≠ 0) (g Θ : Field2)
    (hg : IsMetricField g) (h18 : EntwurfFieldEquations κ g Θ) :
    EntwurfFieldEquationsCov κ g (lowerIndices g Θ) := by
  intro x i j
  have he : entwurfDelta g = fun y => κ • (Θ y + gravStressEnergy κ g y) := by
    funext y
    ext a b
    exact h18 y a b
  have h := congrArg (fun F : Field2 => lowerIndices g F x) he
  rw [lower_operator g hg x, lower_matrix, metric_symm g hg x,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul] at h
  have hs := lower_stress κ g hg x
  rw [lower_matrix, metric_symm g hg x] at hs
  have hl := lower_matrix g Θ x
  rw [metric_symm g hg x] at hl
  rw [hs, ← hl] at h
  have hi := congrFun (congrFun h i) j
  simpa only [Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    add_comm] using hi
