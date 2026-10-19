-- Prove2me | solution 1 for EinsteinGrossmann1913.matterConservation_iff_cov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:07:18.682656+00:00
-- url     : https://prove2.me/submissions/75e4fcc2-e885-4f27-9b3c-7b3ecd5c89ae

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

theorem solution (g Θ : Field2) (hg : IsMetricField g)
    (hΘ : ∀ μ ν : Fin 4, ContDiff ℝ 1 (fun x => Θ x μ ν))
    (hΘsymm : ∀ (x : Coord) (μ ν : Fin 4), Θ x μ ν = Θ x ν μ) :
    MatterConservation g Θ ↔ MatterConservationCov g (lowerIndices g Θ) := by
  have he (σ : Fin 4) (x : Coord) :
      matterConservationCovLHS g (lowerIndices g Θ) σ x =
        matterConservationLHS g Θ σ x := by
    unfold matterConservationCovLHS matterConservationLHS
    rw [divergence_eq g Θ hg hΘ hΘsymm x σ]
    have ht := derivative_pairing g Θ hg x σ
    have hw : (∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => gamma g y μ ν) x *
        lowerIndices g Θ x μ ν) =
        -(∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => g y μ ν) x * Θ x μ ν) := by
      simp only [mul_assoc, ← Finset.mul_sum, ht, mul_neg]
    rw [hw]
    ring
  simp only [MatterConservationCov, MatterConservation, he]
