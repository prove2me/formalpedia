-- Prove2me | solution 1 for EinsteinGrossmann1913.gravitational_energy_momentum_identity_cov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:29:05.055093+00:00
-- url     : https://prove2.me/submissions/c5c61b27-35da-4ffb-bd99-71921e40b285

import Theorems.Thm_EinsteinGrossmann1913_gravitational_energy_momentum_identity
import Theorems.Thm_EinsteinGrossmann1913_fieldEquationsCov_of_fieldEquations

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

private lemma pairing_lower (g Θ : Field2) (hg : IsMetricField g) (x : Coord)
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ i, ∑ j, A i j * lowerIndices g Θ x i j) =
      ∑ i, ∑ j, (g x * A * g x) i j * Θ x i j := by
  change Matrix.trace (A * (lowerIndices g Θ x)ᵀ) =
    Matrix.trace ((g x * A * g x) * (Θ x)ᵀ)
  rw [lower_matrix, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    metric_symm g hg x]
  calc
    _ = Matrix.trace ((A * g x) * (Θ x)ᵀ * g x) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]

private lemma derivative_pairing (g Θ : Field2) (hg : IsMetricField g)
    (x : Coord) (a : Fin 4) :
    (∑ i, ∑ j, pd a (fun y => gamma g y i j) x * lowerIndices g Θ x i j) =
      -(∑ i, ∑ j, pd a (fun y => g y i j) x * Θ x i j) := by
  change (∑ i, ∑ j, md a (gamma g) x i j * lowerIndices g Θ x i j) = _
  rw [pairing_lower g Θ hg x, differentiated_inverse g hg x a]
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, md]

private lemma flux (g Θ : Field2) (hg : IsMetricField g)
    (hΘsymm : ∀ (x : Coord) (i j : Fin 4), Θ x i j = Θ x j i)
    (x : Coord) (σ ν : Fin 4) :
    (∑ μ, gamma g x μ ν * lowerIndices g Θ x μ σ) =
      ∑ μ, g x σ μ * Θ x μ ν := by
  change ((gamma g x)ᵀ * lowerIndices g Θ x) ν σ = _
  rw [inverse_symm g hg x, lower_matrix, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    inverse_mul g hg x, Matrix.one_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [hΘsymm x ν μ]
  ring

private lemma smooth_lower (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ i j : Fin 4, ContDiff ℝ 1 (fun x => Θ x i j)) (i j : Fin 4) :
    ContDiff ℝ 1 (fun x => lowerIndices g Θ x i j) := by
  simp only [lowerIndices, Matrix.of_apply]
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact (((hg.contDiff i a).of_le (by norm_num)).mul
    ((hg.contDiff j b).of_le (by norm_num))).mul (hΘ a b)

private lemma pd_sum (a : Fin 4) (f : Fin 4 → Coord → ℝ) (x : Coord)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    pd a (fun y => ∑ i, f i y) x = ∑ i, pd a (f i) x := by
  unfold pd
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp

private lemma divergence_eq (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ i j : Fin 4, ContDiff ℝ 1 (fun x => Θ x i j))
    (hΘsymm : ∀ (x : Coord) (i j : Fin 4), Θ x i j = Θ x j i)
    (x : Coord) (σ : Fin 4) :
    (∑ μ, ∑ ν, pd ν (fun y => sqrtNegDet g y * gamma g y μ ν *
      lowerIndices g Θ y μ σ) x) =
    ∑ μ, ∑ ν, pd ν (fun y => sqrtNegDet g y * g y σ μ * Θ y μ ν) x := by
  have hgd (i j : Fin 4) := (hg.contDiff i j).differentiable (by norm_num) x
  have hhd (i j : Fin 4) := (smooth_gamma g hg i j).differentiable (by norm_num) x
  have hsd := (smooth_density g hg).differentiable (by norm_num) x
  have htd (i j : Fin 4) := (hΘ i j).differentiable (by norm_num) x
  have hld (i j : Fin 4) := (smooth_lower g Θ hg hΘ i j).differentiable (by norm_num) x
  rw [Finset.sum_comm, Finset.sum_comm (f := fun μ ν => pd ν
    (fun y => sqrtNegDet g y * g y σ μ * Θ y μ ν) x)]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← pd_sum ν (fun μ y => sqrtNegDet g y * gamma g y μ ν * lowerIndices g Θ y μ σ) x
      (fun μ => (hsd.mul (hhd μ ν)).mul (hld μ σ)),
    ← pd_sum ν (fun μ y => sqrtNegDet g y * g y σ μ * Θ y μ ν) x
      (fun μ => (hsd.mul (hgd σ μ)).mul (htd μ ν))]
  congr 1
  funext y
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [flux g Θ hg hΘsymm y σ ν]

private lemma smooth_stress (κ : ℝ) (g : Field2) (hg : IsMetricField g)
    (i j : Fin 4) : ContDiff ℝ 1 (fun x => gravStressEnergy κ g x i j) := by
  classical
  have hg1 (a b : Fin 4) := (hg.contDiff a b).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hh1 (a b : Fin 4) := (smooth_gamma g hg a b).of_le
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdp (a b c : Fin 4) := smooth_pd _ (hg.contDiff b c) a
  have hdq (a b c : Fin 4) := smooth_pd _ (smooth_gamma g hg b c) a
  unfold gravStressEnergy
  simp only [Matrix.of_apply]
  apply contDiff_const.mul
  apply ContDiff.sum
  intro α _
  apply ContDiff.sum
  intro β _
  apply ContDiff.sum
  intro τ _
  apply ContDiff.sum
  intro ρ _
  exact ((((hh1 α i).mul (hh1 β j)).mul (hdp α τ ρ)).mul (hdq β τ ρ)).sub
    ((((contDiff_const.mul (hh1 i j)).mul (hh1 α β)).mul (hdp α τ ρ)).mul (hdq β τ ρ))

private lemma quadratic_symm (g : Field2) (hg : IsMetricField g) (x : Coord) :
    (quadratic g x)ᵀ = quadratic g x := by
  ext a b
  change Matrix.trace (md b g x * (md a (gamma g) x)ᵀ) =
    Matrix.trace (md a g x * (md b (gamma g) x)ᵀ)
  rw [md_symm a _ (inverse_symm g hg) x, md_symm b _ (inverse_symm g hg) x,
    inverse_deriv g hg x a, inverse_deriv g hg x b]
  simp only [Matrix.mul_neg, Matrix.trace_neg]
  congr 1
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (md b g x * gamma g x) (md a g x * gamma g x)

private lemma stress_symm (κ : ℝ) (g : Field2) (hg : IsMetricField g) (x : Coord) :
    (gravStressEnergy κ g x)ᵀ = gravStressEnergy κ g x := by
  rw [stress_matrix κ g hg x]
  simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul,
    inverse_symm g hg x, quadratic_symm g hg x, Matrix.mul_assoc]

private lemma lower_operator (κ : ℝ) (hκ : κ ≠ 0) (g : Field2) (hg : IsMetricField g)
    (x : Coord) : lowerIndices g (entwurfDelta g) x = -entwurfD g x := by
  let Θ : Field2 := fun y => (κ⁻¹ : ℝ) • entwurfDelta g y - gravStressEnergy κ g y
  have heq : EntwurfFieldEquations κ g Θ := by
    intro y i j
    dsimp [Θ]
    simp only [sub_add_cancel]
    field_simp
  have h := fieldEquationsCov_of_fieldEquations κ hκ g Θ hg heq
  have hl : lowerIndices g Θ x =
      (κ⁻¹ : ℝ) • lowerIndices g (entwurfDelta g) x - gravStressEnergyCov κ g x := by
    rw [lower_matrix]
    dsimp [Θ]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [← lower_matrix, ← lower_matrix, lower_stress κ g hg x]
  have hi := h x
  have hm : -entwurfD g x = lowerIndices g (entwurfDelta g) x := by
    ext i j
    have hh := hi i j
    rw [hl] at hh
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hh
    field_simp at hh
    change -entwurfD g x i j = _
    linarith only [hh]
  exact hm.symm

private lemma weighted_pairing (g Θ : Field2) (hg : IsMetricField g)
    (x : Coord) (a : Fin 4) :
    (∑ i, ∑ j, sqrtNegDet g x * pd a (fun y => gamma g y i j) x *
      lowerIndices g Θ x i j) =
      -(∑ i, ∑ j, sqrtNegDet g x * pd a (fun y => g y i j) x * Θ x i j) := by
  simp only [mul_assoc, ← Finset.mul_sum, derivative_pairing g Θ hg x a, mul_neg]

theorem solution (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
        pd ν (fun y => sqrtNegDet g y * gamma g y μ ν * (κ * gravStressEnergyCov κ g y μ σ)) x
      = (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
          sqrtNegDet g x * pd σ (fun y => gamma g y μ ν) x
            * (-entwurfD g x μ ν - κ * gravStressEnergyCov κ g x μ ν) := by
  let Θ : Field2 := fun y => κ • gravStressEnergy κ g y
  have hΘ (i j : Fin 4) : ContDiff ℝ 1 (fun y => Θ y i j) :=
    contDiff_const.mul (smooth_stress κ g hg i j)
  have hΘsymm (y : Coord) (i j : Fin 4) : Θ y i j = Θ y j i := by
    have h := congrFun (congrFun (stress_symm κ g hg y) j) i
    change κ * gravStressEnergy κ g y i j = κ * gravStressEnergy κ g y j i
    rw [show gravStressEnergy κ g y i j = gravStressEnergy κ g y j i from h]
  have hl (y : Coord) : lowerIndices g Θ y = κ • gravStressEnergyCov κ g y := by
    rw [lower_matrix]
    dsimp [Θ]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← lower_matrix, lower_stress κ g hg y]
  have hdiv := divergence_eq g Θ hg hΘ hΘsymm x σ
  simp only [hl, Matrix.smul_apply, smul_eq_mul] at hdiv
  rw [hdiv]
  have h := gravitational_energy_momentum_identity κ hκ g hg σ x
  change (∑ μ, ∑ ν, pd ν (fun y => sqrtNegDet g y * g y σ μ *
    (κ * gravStressEnergy κ g y μ ν)) x) = _
  rw [h]
  congr 1
  have hd := weighted_pairing g (entwurfDelta g) hg x σ
  rw [lower_operator κ hκ g hg x] at hd
  simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib] at hd
  have hs := weighted_pairing g Θ hg x σ
  simp only [hl, Matrix.smul_apply, smul_eq_mul] at hs
  change (∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => g y μ ν) x *
    (-entwurfDelta g x μ ν + κ * gravStressEnergy κ g x μ ν)) = _
  simp only [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  dsimp [Θ] at hs
  linarith only [hd, hs]
