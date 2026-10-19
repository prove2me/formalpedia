-- Prove2me | solution 1 for EinsteinFieldEquationsD.einsteinTensor_symm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:47:28.628477+00:00
-- url     : https://prove2.me/submissions/8e9b080f-8054-43ad-9136-95fddcd343ce

import Theorems.Thm_EinsteinFieldEquationsD_metric_covariantly_constant

open EinsteinFieldEquationsD
open scoped Topology ContDiff Matrix

private lemma smooth_det {D : ℕ} (A : Tensor2 D) (U : Set (Coord D))
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun x => A x a b) U) :
    ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  classical
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

private lemma smooth_inv {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (a b : Fin D) :
    ContDiffOn ℝ ∞ (fun x => invMetric g x a b) U := by
  classical
  have hadj : ContDiffOn ℝ ∞ (fun x => (g x).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    apply smooth_det (fun x => (g x).updateRow b (Pi.single a 1)) U
    intro i j
    by_cases h : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact contDiffOn_const
    · simpa [Matrix.updateRow_apply, h] using hg.smooth i j
  have hdet := (smooth_det g U hg.smooth).inv hg.nondegenerate
  apply (hdet.mul hadj).congr
  intro x _
  simp [invMetric, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply]

private lemma smooth_partial {D : ℕ} (f : Coord D → ℝ) (U : Set (Coord D))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a : Fin D) :
    ContDiffOn ℝ ∞ (fun x => partialDeriv a f x) U := by
  exact (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private lemma smooth_christoffel {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (c a b : Fin D) :
    ContDiffOn ℝ ∞ (fun x => christoffel g x c a b) U := by
  unfold christoffel
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro s _
  exact (smooth_inv g U hg c s).mul
    (((smooth_partial _ U hg.isOpen (hg.smooth s b) a).add
      (smooth_partial _ U hg.isOpen (hg.smooth s a) b)).sub
      (smooth_partial _ U hg.isOpen (hg.smooth a b) s))

private lemma partial_comm {D : ℕ} (f : Coord D → ℝ) (U : Set (Coord D))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (x : Coord D) (hx : x ∈ U)
    (a b : Fin D) :
    partialDeriv a (fun y => partialDeriv b f y) x =
      partialDeriv b (fun y => partialDeriv a f y) x := by
  have hlocal := hf.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hlocal.fderiv_right (m := 1) (by decide)).differentiableAt (by norm_num)
  have h (v : Coord D) :
      fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    simpa using fderiv_clm_apply hd (differentiableAt_const v)
  unfold partialDeriv
  rw [h, h]
  exact (hlocal.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)).eq _ _

private noncomputable def md {D : ℕ} (a : Fin D) (F : Tensor2 D) : Tensor2 D :=
  fun x i j => partialDeriv a (fun y => F y i j) x

private lemma md_add {D : ℕ} (a : Fin D) (F G : Tensor2 D) (x : Coord D)
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    md a (F + G) x = md a F x + md a G x := by
  ext i j
  exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single a 1))
    ((hF i j).hasFDerivAt.add (hG i j).hasFDerivAt).fderiv

private lemma md_mul {D : ℕ} (a : Fin D) (F G : Tensor2 D) (x : Coord D)
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    md a (fun y => F y * G y) x = md a F x * G x + F x * md a G x := by
  classical
  ext i j
  simp only [md, partialDeriv, Matrix.mul_apply]
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => F y i k * G y k j) (fun k _ => (hF i k).mul (hG k j))]
  simp only [sum_apply, Matrix.add_apply, Matrix.mul_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [md, partialDeriv]
  rw [fderiv_fun_mul (c := fun y => F y i k) (d := fun y => G y k j) (hF i k) (hG k j)]
  simp [smul_eq_mul, mul_comm, add_comm]

private noncomputable def conn {D : ℕ} (g : Tensor2 D) (b : Fin D) : Tensor2 D :=
  fun x m a => christoffel g x m a b

private noncomputable def curv {D : ℕ} (g : Tensor2 D) (b c : Fin D) : Tensor2 D :=
  md b (conn g c) - md c (conn g b) +
    (fun x => conn g b x * conn g c x) - (fun x => conn g c x * conn g b x)

private lemma christoffel_symm {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (m a b : Fin D) :
    christoffel g x m a b = christoffel g x m b a := by
  have h (s : Fin D) : partialDeriv s (fun y => g y a b) x =
      partialDeriv s (fun y => g y b a) x := by
    have he : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => g y b a) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact hg.symm y hy a b
    exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single s 1)) he.fderiv_eq
  unfold christoffel
  simp_rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma curv_apply {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (m a b c : Fin D) :
    curv g b c x m a = riemann g x m a b c := by
  classical
  simp only [curv, conn, md, Pi.sub_apply, Pi.add_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_apply, riemann, Finset.sum_sub_distrib]
  simp_rw [christoffel_symm g U hg x hx _ a c, christoffel_symm g U hg x hx _ a b]
  ring

private lemma md_transpose {D : ℕ} (a : Fin D) (F : Tensor2 D) (x : Coord D) :
    md a (fun y => (F y)ᵀ) x = (md a F x)ᵀ := rfl

private lemma matrix_compat {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (a : Fin D) :
    md a g x = (conn g a x)ᵀ * g x + g x * conn g a x := by
  classical
  ext i j
  have h := metric_covariantly_constant g U hg x hx a i j
  simp only [covDeriv2] at h
  simp only [md, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, conn]
  simp_rw [christoffel_symm g U hg x hx _ i a, christoffel_symm g U hg x hx _ j a]
  simp_rw [mul_comm (g x i _) (christoffel g x _ a j)]
  rw [← Finset.sum_add_distrib]
  linarith

private lemma differentiated_compat {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (a b : Fin D) :
    md b (md a g) x = (md b (conn g a) x)ᵀ * g x +
      (conn g a x)ᵀ * md b g x + md b g x * conn g a x +
      g x * md b (conn g a) x := by
  have hA (i j : Fin D) : DifferentiableAt ℝ (fun y => conn g a y i j) x :=
    (smooth_christoffel g U hg i j a).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have hG (i j : Fin D) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.smooth i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hP (i j : Fin D) : DifferentiableAt ℝ (fun y => ((conn g a y)ᵀ * g y) i j) x := by
    classical
    change DifferentiableAt ℝ (fun y => ∑ s, conn g a y s i * g y s j) x
    exact DifferentiableAt.fun_sum fun s _ => (hA s i).mul (hG s j)
  have hQ (i j : Fin D) : DifferentiableAt ℝ (fun y => (g y * conn g a y) i j) x := by
    classical
    change DifferentiableAt ℝ (fun y => ∑ s, g y i s * conn g a y s j) x
    exact DifferentiableAt.fun_sum fun s _ => (hG i s).mul (hA s j)
  have he : md b (md a g) x =
      md b ((fun y => (conn g a y)ᵀ * g y) + (fun y => g y * conn g a y)) x := by
    ext i j
    have he : (fun y => md a g y i j) =ᶠ[𝓝 x]
        (fun y => ((conn g a y)ᵀ * g y + g y * conn g a y) i j) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M i j)
        (matrix_compat g U hg y hy a)
    exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single b 1)) he.fderiv_eq
  rw [he, md_add b _ _ x hP hQ, md_mul b (fun y => (conn g a y)ᵀ) g x (fun i j => hA j i) hG,
    md_mul b g _ x hG hA, md_transpose]
  abel

private lemma curvature_metric_skew {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (b c : Fin D) :
    (curv g b c x)ᵀ * g x + g x * curv g b c x = 0 := by
  have hcomm : md b (md c g) x = md c (md b g) x := by
    ext i j
    exact partial_comm _ U hg.isOpen (hg.smooth i j) x hx b c
  rw [differentiated_compat g U hg x hx, differentiated_compat g U hg x hx,
    matrix_compat g U hg x hx, matrix_compat g U hg x hx] at hcomm
  simp only [curv, Pi.add_apply, Pi.sub_apply, Matrix.transpose_add,
    Matrix.transpose_sub, Matrix.transpose_mul]
  convert sub_eq_zero.mpr hcomm using 1
  noncomm_ring

private lemma curvature_trace_zero {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (b c : Fin D) :
    ∑ m, riemann g x m m b c = 0 := by
  have hi : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx))
  have hi' : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx))
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => Matrix.trace ((g x)⁻¹ * M))
    (curvature_metric_skew g U hg x hx b c)
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_add,
    Matrix.trace_mul_cycle, hi, Matrix.one_mul, hi', Matrix.one_mul] at h
  simp only [Matrix.mul_zero, Matrix.trace_zero, Matrix.trace_transpose] at h
  have hz : Matrix.trace (curv g b c x) = 0 := by linarith
  simpa only [Matrix.trace, Matrix.diag, curv_apply g U hg x hx] using hz

private lemma first_bianchi {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (m a b c : Fin D) :
    riemann g x m a b c + riemann g x m b c a + riemann g x m c a b = 0 := by
  have hd (l i j : Fin D) :
      partialDeriv l (fun y => christoffel g y m i j) x =
        partialDeriv l (fun y => christoffel g y m j i) x := by
    have he : (fun y => christoffel g y m i j) =ᶠ[𝓝 x]
        (fun y => christoffel g y m j i) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact christoffel_symm g U hg y hy m i j
    exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single l 1)) he.fderiv_eq
  have hsum :
      (∑ s, (christoffel g x m s b * christoffel g x s c a -
        christoffel g x m s c * christoffel g x s b a)) +
      (∑ s, (christoffel g x m s c * christoffel g x s a b -
        christoffel g x m s a * christoffel g x s c b)) +
      (∑ s, (christoffel g x m s a * christoffel g x s b c -
        christoffel g x m s b * christoffel g x s a c)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s _
    rw [christoffel_symm g U hg x hx s c a,
      christoffel_symm g U hg x hx s b a, christoffel_symm g U hg x hx s c b]
    ring
  simp only [riemann]
  rw [hd b a c, hd c b a, hd a c b]
  linarith

private lemma riemann_skew {D : ℕ} (g : Tensor2 D) (x : Coord D) (m a b c : Fin D) :
    riemann g x m a b c = -riemann g x m a c b := by
  classical
  simp only [riemann, Finset.sum_sub_distrib]
  ring

private lemma ricci_symm {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (a b : Fin D) :
    ricci g x a b = ricci g x b a := by
  have h := Finset.sum_eq_zero (s := Finset.univ) fun c _ => first_bianchi g U hg x hx c a c b
  simp only [Finset.sum_add_distrib] at h
  simp_rw [riemann_skew g x _ b a _, riemann_skew g x _ _ b a] at h
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, curvature_trace_zero g U hg x hx] at h
  unfold ricci
  linarith

theorem solution {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ a b : Fin D, einsteinTensor g x a b = einsteinTensor g x b a := by
  intro x hx a b
  simp only [einsteinTensor, ricci_symm g U hg x hx a b, hg.symm x hx a b]
