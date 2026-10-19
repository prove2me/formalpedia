-- Prove2me | solution 1 for EinsteinGrossmann1913.gravitational_energy_momentum_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:41:17.11065+00:00
-- url     : https://prove2.me/submissions/64b21cb9-1703-4e49-907f-b17892a635f6

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


private lemma pd_sum (a : Fin 4) (f : Fin 4 → Coord → ℝ) (x : Coord)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    pd a (fun y => ∑ i, f i y) x = ∑ i, pd a (f i) x := by
  unfold pd
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp

private lemma pd_mul (a : Fin 4) (f h : Coord → ℝ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    pd a (fun y => f y * h y) x = pd a f x * h x + f x * pd a h x := by
  unfold pd
  rw [fderiv_fun_mul hf hh]
  simp [smul_eq_mul, mul_comm, add_comm]

private lemma pd_comm (f : Coord → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Coord) (a b : Fin 4) :
    pd a (fun y => pd b f y) x = pd b (fun y => pd a f y) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h (v : Coord) : fderiv ℝ (fun y => fderiv ℝ f y v) x =
      (fderiv ℝ (fderiv ℝ f) x).flip v := by
    simpa using fderiv_clm_apply hd (differentiableAt_const v)
  unfold pd
  rw [h, h]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq _ _

private lemma det_deriv (g : Field2) (hg : IsMetricField g) (x : Coord) (a : Fin 4) :
    pd a (fun y => (g y).det) x =
      (g x).det * Matrix.trace (gamma g x * md a g x) := by
  let D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin 4 → ℝ) ℝ :=
    { Matrix.detRowAlternating.toMultilinearMap with
      cont := continuous_id.matrix_det }
  have hgd : DifferentiableAt ℝ (fun y i j => g y i j) x :=
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
      (hg.contDiff i j).differentiable (by norm_num) x
  have he := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single a 1))
    ((D.hasFDerivAt (fun i j => g x i j)).comp x hgd.hasFDerivAt).fderiv
  change pd a (fun y => (g y).det) x = _ at he
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply] at he
  have hrow (i : Fin 4) :
      Function.update (g x) i ((fderiv ℝ (fun y i j => g y i j) x (Pi.single a 1)) i) =
      (g x).updateRow i (∑ k, (md a g x * gamma g x) i k • g x k) := by
    have hfd : fderiv ℝ (fun y i j => g y i j) x (Pi.single a 1) = md a g x := by
      ext k l
      have hd (i j : Fin 4) := (hg.contDiff i j).differentiable (by norm_num) x
      simp only [fderiv_pi (fun i => differentiableAt_pi.mpr (hd i)),
        ContinuousLinearMap.pi_apply, fderiv_pi (hd k), md, pd]
    rw [hfd]
    congr 1
    have hi := congrFun (congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i)
      (show (md a g x * gamma g x) * g x = md a g x by
        rw [Matrix.mul_assoc, inverse_mul g hg x, Matrix.mul_one]))
    ext j
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hi j).symm
  rw [he]
  simp_rw [hrow]
  change (∑ i, ((g x).updateRow i (∑ k, (md a g x * gamma g x) i k • g x k)).det) = _
  simp_rw [Matrix.det_updateRow_sum]
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul]
  change Matrix.trace (md a g x * gamma g x) * (g x).det = _
  rw [Matrix.trace_mul_comm]
  ring

private lemma density_deriv (g : Field2) (hg : IsMetricField g) (x : Coord) (a : Fin 4) :
    pd a (sqrtNegDet g) x =
      (1 / 2) * sqrtNegDet g x * Matrix.trace (gamma g x * md a g x) := by
  have hS : sqrtNegDet g x ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hg.det_neg x)))
  have hsq : sqrtNegDet g x ^ 2 = -(g x).det :=
    Real.sq_sqrt (le_of_lt (neg_pos.mpr (hg.det_neg x)))
  unfold sqrtNegDet pd
  rw [fderiv_sqrt ((smooth_det g hg).neg.differentiable (by norm_num) x)
    (neg_ne_zero.mpr (ne_of_lt (hg.det_neg x))), fderiv_fun_neg]
  change (1 / (2 * sqrtNegDet g x)) * (-pd a (fun y => (g y).det) x) = _
  rw [det_deriv g hg x a]
  change (1 / (2 * sqrtNegDet g x)) * (-((g x).det * _)) =
    1 / 2 * sqrtNegDet g x * _
  have hd : (g x).det = -(sqrtNegDet g x ^ 2) := by linarith only [hsq]
  rw [hd]
  field_simp [hS]

private noncomputable def pair (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := Matrix.trace (A * B)

private lemma pair_components (A B : Matrix (Fin 4) (Fin 4) ℝ) (hB : Bᵀ = B) :
    pair A B = ∑ i, ∑ j, A i j * B i j := by
  unfold pair Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := congrFun (congrFun hB i) j
  simp only [Matrix.transpose_apply] at h
  rw [h]

private lemma pair_comm (A B : Matrix (Fin 4) (Fin 4) ℝ) : pair A B = pair B A :=
  Matrix.trace_mul_comm _ _

private lemma quadratic_trace (g : Field2) (hg : IsMetricField g) (x : Coord) (a b : Fin 4) :
    quadratic g x a b = pair (md a g x) (md b (gamma g) x) := by
  rw [pair_components _ _ (md_symm b _ (inverse_symm g hg) x)]
  rfl

private lemma pair_deriv (a : Fin 4) (F G : Field2) (x : Coord)
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    pd a (fun y => pair (F y) (G y)) x = pair (md a F x) (G x) + pair (F x) (md a G x) := by
  unfold pair Matrix.trace
  change pd a (fun y => ∑ i, (F y * G y) i i) x = _
  rw [pd_sum a (fun i y => (F y * G y) i i) x (fun i => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun j _ => (hF i j).mul (hG j i))]
  have hm := md_mul a F G x hF hG
  change (∑ i, md a (fun y => F y * G y) x i i) = _
  rw [hm]
  simp [Finset.sum_add_distrib]

private lemma second_trace (g : Field2) (hg : IsMetricField g) (x : Coord) (σ a b : Fin 4) :
    pair (md a g x) (md σ (md b (gamma g)) x) =
      pair (md σ (md b g) x) (md a (gamma g) x) +
      pair (md σ g x) (md b (gamma g) x * g x * md a (gamma g) x) +
      pair (md σ g x) (md a (gamma g) x * g x * md b (gamma g) x) := by
  have he := weighted_second_inverse g hg σ b (fun _ => 1) contDiff_const x
  simp only [one_smul] at he
  calc
    _ = -Matrix.trace (md a (gamma g) x *
        (g x * md σ (md b (gamma g)) x * g x)) := by
      have ha : md a g x = -(g x * md a (gamma g) x * g x) := by
        simpa using (congrArg Neg.neg (differentiated_inverse g hg x a)).symm
      rw [ha]
      unfold pair
      simp only [Matrix.neg_mul, Matrix.trace_neg]
      congr 1
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (g x) (md a (gamma g) x * g x * md σ (md b (gamma g)) x)
    _ = _ := by
      rw [he]
      have hb : md b g x = -(g x * md b (gamma g) x * g x) := by
        simpa using (congrArg Neg.neg (differentiated_inverse g hg x b)).symm
      rw [hb]
      simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_assoc, Matrix.trace_add, Matrix.trace_neg]
      simp only [← Matrix.mul_assoc (gamma g x) (g x),
        ← Matrix.mul_assoc (g x) (gamma g x), inverse_mul g hg x, mul_inverse g hg x,
        Matrix.one_mul]
      unfold pair
      rw [Matrix.trace_mul_comm (md a (gamma g) x) (md σ (md b g) x)]
      have ht := Matrix.trace_mul_comm (md a (gamma g) x)
        (md σ g x * (md b (gamma g) x * g x))
      simp only [Matrix.mul_assoc] at ht ⊢
      rw [ht]
      have ht2 := Matrix.trace_mul_cycle (md a (gamma g) x * g x)
        (md b (gamma g) x) (md σ g x)
      simp only [Matrix.mul_assoc] at ht2
      rw [ht2]
      ring

private noncomputable def scalarEnergy (g : Field2) (x : Coord) : ℝ :=
  ∑ a, ∑ b, gamma g x a b * quadratic g x a b

private noncomputable def nonlinear (g : Field2) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ a, ∑ b, gamma g x a b • (md a (gamma g) x * g x * md b (gamma g) x)

private noncomputable def rawLaplace (g : Field2) (x : Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ a, ∑ b, md a (fun y => (gamma g y a b * sqrtNegDet g y) • md b (gamma g) y) x

private noncomputable def hessianEnergy (g : Field2) (σ : Fin 4) (x : Coord) : ℝ :=
  ∑ a, ∑ b, gamma g x a b * pair (md σ (md a g) x) (md b (gamma g) x)

private lemma smooth_Q (g : Field2) (hg : IsMetricField g) (a b : Fin 4) :
    ContDiff ℝ 1 (fun x => quadratic g x a b) := by
  unfold quadratic md
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (smooth_pd _ (hg.contDiff i j) a).mul (smooth_pd _ (smooth_gamma g hg i j) b)

private lemma smooth_E (g : Field2) (hg : IsMetricField g) : ContDiff ℝ 1 (scalarEnergy g) := by
  unfold scalarEnergy
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ((smooth_gamma g hg a b).of_le (by norm_num)).mul (smooth_Q g hg a b)

private lemma symm_sum (g : Field2) (hg : IsMetricField g) (x : Coord)
    (f : Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, gamma g x a b * f b a) = ∑ a, ∑ b, gamma g x a b * f a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h := congrFun (congrFun (inverse_symm g hg x) a) b
  simp only [Matrix.transpose_apply] at h
  rw [h]

private lemma scalarEnergy_deriv (g : Field2) (hg : IsMetricField g) (x : Coord) (σ : Fin 4) :
    pd σ (scalarEnergy g) x =
      (∑ a, ∑ b, md σ (gamma g) x a b * quadratic g x a b) +
      2 * hessianEnergy g σ x + 2 * pair (md σ g x) (nonlinear g x) := by
  have hgd (i j : Fin 4) := (hg.contDiff i j).differentiable (by norm_num) x
  have hhd (i j : Fin 4) := (smooth_gamma g hg i j).differentiable (by norm_num) x
  have hpd (a i j : Fin 4) := (smooth_pd _ (hg.contDiff i j) a).differentiable (by norm_num) x
  have hqd (a i j : Fin 4) := (smooth_pd _ (smooth_gamma g hg i j) a).differentiable (by norm_num) x
  have hQ (a b : Fin 4) : pd σ (fun y => quadratic g y a b) x =
      pair (md σ (md a g) x) (md b (gamma g) x) +
      pair (md σ (md b g) x) (md a (gamma g) x) +
      pair (md σ g x) (md b (gamma g) x * g x * md a (gamma g) x) +
      pair (md σ g x) (md a (gamma g) x * g x * md b (gamma g) x) := by
    have he : (fun y => quadratic g y a b) =
        fun y => pair (md a g y) (md b (gamma g) y) :=
      funext fun y => quadratic_trace g hg y a b
    rw [he, pair_deriv σ (md a g) (md b (gamma g)) x (hpd a) (hqd b), second_trace g hg x σ a b]
    ring
  unfold scalarEnergy
  rw [pd_sum σ (fun a y => ∑ b, gamma g y a b * quadratic g y a b) x
    (fun a => DifferentiableAt.fun_sum fun b _ =>
      (hhd a b).mul ((smooth_Q g hg a b).differentiable (by norm_num) x))]
  simp_rw [pd_sum σ (fun b y => gamma g y _ b * quadratic g y _ b) x
    (fun b => (hhd _ b).mul ((smooth_Q g hg _ b).differentiable (by norm_num) x))]
  simp_rw [pd_mul σ (fun y => gamma g y _ _) (fun y => quadratic g y _ _) x
    (hhd _ _) ((smooth_Q g hg _ _).differentiable (by norm_num) x), hQ]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [symm_sum g hg x (fun a b => pair (md σ (md a g) x) (md b (gamma g) x)),
    symm_sum g hg x (fun a b => pair (md σ g x)
      (md a (gamma g) x * g x * md b (gamma g) x))]
  unfold hessianEnergy nonlinear pair
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, md]
  ring

private lemma operator_form (g : Field2) (hg : IsMetricField g) (x : Coord) :
    entwurfDelta g x = (1 / sqrtNegDet g x) • rawLaplace g x - nonlinear g x := by
  ext i j
  simp only [entwurfDelta, Matrix.of_apply, Matrix.sub_apply, rawLaplace, nonlinear,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, md, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, md]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  have hs := congrFun (congrFun (md_symm b _ (inverse_symm g hg) x) t) j
  simp only [Matrix.transpose_apply, md] at hs
  rw [hs]
  ring

private lemma scaled_stress (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (x : Coord) :
    κ • gravStressEnergy κ g x = -(1 / 2 : ℝ) •
      (gamma g x * quadratic g x * gamma g x - (1 / 2 * scalarEnergy g x) • gamma g x) := by
  rw [stress_matrix κ g hg x, smul_smul]
  congr 1
  field_simp

private lemma stress_pair (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (x : Coord) (σ : Fin 4) :
    pair (md σ g x) (κ • gravStressEnergy κ g x) =
      (1 / 2) * (∑ a, ∑ b, md σ (gamma g) x a b * quadratic g x a b) +
      (1 / 4) * scalarEnergy g x * Matrix.trace (gamma g x * md σ g x) := by
  have he : pair (md σ g x) (gamma g x * quadratic g x * gamma g x) =
      -pair (md σ (gamma g) x) (quadratic g x) := by
    unfold pair
    rw [inverse_deriv g hg x σ]
    simp only [Matrix.neg_mul, Matrix.trace_neg, neg_neg]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm
      (md σ g x * gamma g x * quadratic g x) (gamma g x)
  have hp : pair (md σ (gamma g) x) (quadratic g x) =
      ∑ a, ∑ b, md σ (gamma g) x a b * quadratic g x a b := by
    rw [pair_comm, pair_components _ _ (md_symm σ _ (inverse_symm g hg) x)]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [scaled_stress κ hκ g hg x]
  change Matrix.trace (md σ g x * (_ • _)) = _
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
    smul_eq_mul]
  change -(1 / 2 : ℝ) * (pair (md σ g x) (gamma g x * quadratic g x * gamma g x) -
    (1 / 2 * scalarEnergy g x) * pair (md σ g x) (gamma g x)) = _
  rw [he, hp, pair_comm (md σ g x) (gamma g x)]
  unfold pair
  ring

private lemma flux_energy (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (x : Coord) (σ ν : Fin 4) :
    (∑ μ, sqrtNegDet g x * g x σ μ * (κ * gravStressEnergy κ g x μ ν)) =
      -(1 / 2 : ℝ) * (∑ b, pair (md σ g x)
        ((gamma g x ν b * sqrtNegDet g x) • md b (gamma g) x)) +
      (1 / 4) * (sqrtNegDet g x * scalarEnergy g x) * (1 : Matrix (Fin 4) (Fin 4) ℝ) σ ν := by
  have he : g x * (κ • gravStressEnergy κ g x) = -(1 / 2 : ℝ) •
      (quadratic g x * gamma g x - (1 / 2 * scalarEnergy g x) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [scaled_stress κ hκ g hg x, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul,
      ← Matrix.mul_assoc, mul_inverse g hg x]
    simp only [← Matrix.mul_assoc, mul_inverse g hg x, Matrix.one_mul]
  have hi := congrFun (congrFun he σ) ν
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at hi
  have hl : (∑ μ, sqrtNegDet g x * g x σ μ * (κ * gravStressEnergy κ g x μ ν)) =
      sqrtNegDet g x * ∑ μ, g x σ μ * (κ * gravStressEnergy κ g x μ ν) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    ring
  have hsym (b : Fin 4) : gamma g x b ν = gamma g x ν b := by
    have h := congrFun (congrFun (inverse_symm g hg x) b) ν
    exact h.symm
  simp_rw [hsym] at hi
  have hp : (∑ b, pair (md σ g x)
      ((gamma g x ν b * sqrtNegDet g x) • md b (gamma g) x)) =
      sqrtNegDet g x * ∑ b, quadratic g x σ b * gamma g x ν b := by
    simp only [pair, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [quadratic_trace g hg x σ b]
    unfold pair
    ring
  rw [hl, hi, hp]
  ring


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

private lemma smooth_pair (F G : Field2)
    (hF : ∀ i j, ContDiff ℝ 1 (fun y => F y i j))
    (hG : ∀ i j, ContDiff ℝ 1 (fun y => G y i j)) :
    ContDiff ℝ 1 (fun y => pair (F y) (G y)) := by
  unfold pair Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hF i j).mul (hG j i)

private lemma pd_linear (a : Fin 4) (f h : Coord → ℝ) (x : Coord) (c d : ℝ)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    pd a (fun y => c * f y + d * h y) x = c * pd a f x + d * pd a h x := by
  unfold pd
  rw [fderiv_fun_add (hf.const_mul c) (hh.const_mul d),
    fderiv_const_mul hf, fderiv_const_mul hh]
  simp only [add_apply, smul_apply, smul_eq_mul]

private lemma divergence_energy (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (x : Coord) (σ : Fin 4) :
    (∑ μ, ∑ ν, pd ν (fun y => sqrtNegDet g y * g y σ μ *
      (κ * gravStressEnergy κ g y μ ν)) x) =
      -(1 / 2 : ℝ) * pair (md σ g x) (rawLaplace g x) -
      (1 / 2 : ℝ) * sqrtNegDet g x * hessianEnergy g σ x +
      (1 / 4 : ℝ) * pd σ (fun y => sqrtNegDet g y * scalarEnergy g y) x := by
  let W (a b : Fin 4) : Field2 :=
    fun y => (gamma g y a b * sqrtNegDet g y) • md b (gamma g) y
  let K : Coord → ℝ := fun y => sqrtNegDet g y * scalarEnergy g y
  have hG (i j : Fin 4) := smooth_pd _ (hg.contDiff i j) σ
  have hW (a b i j : Fin 4) : ContDiff ℝ 1 (fun y => W a b y i j) :=
    ((((smooth_gamma g hg a b).of_le (by norm_num)).mul
      ((smooth_density g hg).of_le (by norm_num))).mul
      (smooth_pd _ (smooth_gamma g hg i j) b))
  have hK : DifferentiableAt ℝ K x :=
    ((smooth_density g hg).differentiable (by norm_num) x).mul
      ((smooth_E g hg).differentiable (by norm_num) x)
  have hf (ν : Fin 4) : DifferentiableAt ℝ
      (fun y => ∑ b, pair (md σ g y) (W ν b y)) x :=
    DifferentiableAt.fun_sum fun b _ =>
      (smooth_pair (md σ g) (W ν b) hG (hW ν b)).differentiable (by norm_num) x
  have hterms (ν : Fin 4) :
      (∑ μ, pd ν (fun y => sqrtNegDet g y * g y σ μ *
        (κ * gravStressEnergy κ g y μ ν)) x) =
      -(1 / 2 : ℝ) * (∑ b, (pair (md ν (md σ g) x) (W ν b x) +
        pair (md σ g x) (md ν (W ν b) x))) +
      (1 / 4 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) σ ν * pd ν K x := by
    rw [← pd_sum ν (fun μ y => sqrtNegDet g y * g y σ μ *
      (κ * gravStressEnergy κ g y μ ν)) x (fun μ =>
        (((smooth_density g hg).differentiable (by norm_num) x).mul
          ((hg.contDiff σ μ).differentiable (by norm_num) x)).mul
          (((smooth_stress κ g hg μ ν).differentiable (by norm_num) x).const_mul κ))]
    have he : (fun y => ∑ μ, sqrtNegDet g y * g y σ μ *
        (κ * gravStressEnergy κ g y μ ν)) = fun y =>
        -(1 / 2 : ℝ) * (∑ b, pair (md σ g y) (W ν b y)) +
        ((1 / 4 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) σ ν) * K y := by
      funext y
      rw [flux_energy κ hκ g hg y σ ν]
      dsimp [W, K]
      ring
    rw [he, pd_linear ν _ K x _ _ (hf ν) hK,
      pd_sum ν (fun b y => pair (md σ g y) (W ν b y)) x (fun b =>
        (smooth_pair (md σ g) (W ν b) hG (hW ν b)).differentiable (by norm_num) x)]
    simp_rw [pair_deriv ν (md σ g) (W ν _) x
      (fun i j => (hG i j).differentiable (by norm_num) x)
      (fun i j => (hW ν _ i j).differentiable (by norm_num) x)]
  have hc (a : Fin 4) : md a (md σ g) x = md σ (md a g) x := by
    ext i j
    exact pd_comm _ (hg.contDiff i j) x a σ
  have hess : (∑ a, ∑ b, pair (md a (md σ g) x) (W a b x)) =
      sqrtNegDet g x * hessianEnergy g σ x := by
    simp_rw [hc]
    unfold W hessianEnergy pair
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hlap : (∑ a, ∑ b, pair (md σ g x) (md a (W a b) x)) =
      pair (md σ g x) (rawLaplace g x) := by
    simp only [rawLaplace, W, pair, Matrix.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_comm]
  simp_rw [hterms]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hess, hlap]
  have hdiag : (∑ ν, (1 / 4 : ℝ) * (1 : Matrix (Fin 4) (Fin 4) ℝ) σ ν * pd ν K x) = (1 / 4 : ℝ) * pd σ K x := by
    simp [Matrix.one_apply]
  rw [hdiag]
  ring

theorem solution (κ : ℝ) (hκ : κ ≠ 0) (g : Field2)
    (hg : IsMetricField g) (σ : Fin 4) (x : Coord) :
    ∑ μ : Fin 4, ∑ ν : Fin 4,
        pd ν (fun y => sqrtNegDet g y * g y σ μ * (κ * gravStressEnergy κ g y μ ν)) x
      = (1 / 2) * ∑ μ : Fin 4, ∑ ν : Fin 4,
          sqrtNegDet g x * pd σ (fun y => g y μ ν) x
            * (-entwurfDelta g x μ ν + κ * gravStressEnergy κ g x μ ν) := by
  have hS : sqrtNegDet g x ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hg.det_neg x)))
  have hpair : (∑ μ, ∑ ν, sqrtNegDet g x * pd σ (fun y => g y μ ν) x *
      (-entwurfDelta g x μ ν + κ * gravStressEnergy κ g x μ ν)) =
      sqrtNegDet g x * pair (md σ g x) (-entwurfDelta g x + κ • gravStressEnergy κ g x) := by
    rw [pair_comm, pair_components _ _ (md_symm σ _ (metric_symm g hg) x)]
    simp only [Finset.mul_sum, Matrix.add_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul, md]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    ring
  rw [divergence_energy κ hκ g hg x σ, hpair]
  have hR : (1 / 2 : ℝ) * (sqrtNegDet g x *
      pair (md σ g x) (-entwurfDelta g x + κ • gravStressEnergy κ g x)) =
      -(1 / 2 : ℝ) * pair (md σ g x) (rawLaplace g x) +
      (1 / 2 : ℝ) * sqrtNegDet g x * pair (md σ g x) (nonlinear g x) +
      (1 / 2 : ℝ) * sqrtNegDet g x * pair (md σ g x) (κ • gravStressEnergy κ g x) := by
    rw [operator_form g hg x]
    unfold pair
    simp only [neg_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    field_simp [hS]
    ring
  rw [hR, stress_pair κ hκ g hg x σ,
    pd_mul σ (sqrtNegDet g) (scalarEnergy g) x
      ((smooth_density g hg).differentiable (by norm_num) x)
      ((smooth_E g hg).differentiable (by norm_num) x),
    density_deriv g hg x σ, scalarEnergy_deriv g hg x σ]
  ring
