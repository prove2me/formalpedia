-- Prove2me | solution 1 for EinsteinFieldEquationsD.einsteinTensor_divergence_free
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:57:50.786976+00:00
-- url     : https://prove2.me/submissions/4e3748dc-faa0-45ac-b0c3-2b6998b5f4e7

import Theorems.Thm_EinsteinFieldEquationsD_metric_covariantly_constant
import Theorems.Thm_EinsteinFieldEquationsD_differential_bianchi_identity
import Theorems.Thm_EinsteinFieldEquationsD_einsteinTensor_symm

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

private lemma smooth_riemann {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (m a b c : Fin D) :
    ContDiffOn ℝ ∞ (fun x => riemann g x m a b c) U := by
  unfold riemann
  exact ((smooth_partial _ U hg.isOpen (smooth_christoffel g U hg m a c) b).sub
    (smooth_partial _ U hg.isOpen (smooth_christoffel g U hg m a b) c)).add
    (ContDiffOn.sum fun s _ => ((smooth_christoffel g U hg m s b).mul
      (smooth_christoffel g U hg s c a)).sub
      ((smooth_christoffel g U hg m s c).mul (smooth_christoffel g U hg s b a)))

private lemma smooth_curv {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (b c i j : Fin D) :
    ContDiffOn ℝ ∞ (fun x => curv g b c x i j) U := by
  apply (smooth_riemann g U hg i j b c).congr
  intro x hx
  exact curv_apply g U hg x hx i j b c

private lemma smooth_ricci {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (a b : Fin D) :
    ContDiffOn ℝ ∞ (fun x => ricci g x a b) U :=
  ContDiffOn.sum fun c _ => smooth_riemann g U hg c a c b

private lemma parallel_skew {D : ℕ} (g F : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (hF : ∀ i j, ContDiffOn ℝ ∞ (fun x => F x i j) U)
    (hsk : ∀ x ∈ U, (F x)ᵀ * g x + g x * F x = 0)
    (x : Coord D) (hx : x ∈ U) (e : Fin D) :
    let B := md e F x + conn g e x * F x - F x * conn g e x
    Bᵀ * g x + g x * B = 0 := by
  have hFd (i j : Fin D) : DifferentiableAt ℝ (fun y => F y i j) x :=
    (hF i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hgd (i j : Fin D) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.smooth i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hp (i j : Fin D) : DifferentiableAt ℝ (fun y => ((F y)ᵀ * g y) i j) x := by
    classical
    change DifferentiableAt ℝ (fun y => ∑ s, F y s i * g y s j) x
    exact DifferentiableAt.fun_sum fun s _ => (hFd s i).mul (hgd s j)
  have hq (i j : Fin D) : DifferentiableAt ℝ (fun y => (g y * F y) i j) x := by
    classical
    change DifferentiableAt ℝ (fun y => ∑ s, g y i s * F y s j) x
    exact DifferentiableAt.fun_sum fun s _ => (hgd i s).mul (hFd s j)
  have he : md e ((fun y => (F y)ᵀ * g y) + (fun y => g y * F y)) x = 0 := by
    ext i j
    have he : (fun y => ((F y)ᵀ * g y + g y * F y) i j) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M i j) (hsk y hy)
    simpa [md, partialDeriv] using
      congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single e 1)) he.fderiv_eq
  rw [md_add _ _ _ _ hp hq,
    md_mul e (fun y => (F y)ᵀ) g x (fun i j => hFd j i) hgd,
    md_mul e g F x hgd hFd, md_transpose, matrix_compat g U hg x hx] at he
  dsimp only
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
  calc
    _ = ((md e F x)ᵀ * g x + (F x)ᵀ *
          ((conn g e x)ᵀ * g x + g x * conn g e x) +
          (((conn g e x)ᵀ * g x + g x * conn g e x) * F x + g x * md e F x)) -
        (conn g e x)ᵀ * ((F x)ᵀ * g x + g x * F x) -
        ((F x)ᵀ * g x + g x * F x) * conn g e x := by noncomm_ring
    _ = 0 := by rw [he, hsk x hx]; simp

private noncomputable def cr {D : ℕ} (g : Tensor2 D) (x : Coord D)
    (e b c : Fin D) : Matrix (Fin D) (Fin D) ℝ :=
  fun m a => covDerivRiemann g x e m a b c

private lemma cr_formula {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e b c : Fin D) :
    cr g x e b c = md e (curv g b c) x + conn g e x * curv g b c x -
      curv g b c x * conn g e x -
      ∑ s, christoffel g x s e b • curv g s c x -
      ∑ s, christoffel g x s e c • curv g b s x := by
  classical
  have hd (m a : Fin D) : md e (curv g b c) x m a =
      partialDeriv e (fun y => riemann g y m a b c) x := by
    have he : (fun y => curv g b c y m a) =ᶠ[𝓝 x]
        (fun y => riemann g y m a b c) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact curv_apply g U hg y hy m a b c
    exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single e 1)) he.fderiv_eq
  ext m a
  simp only [cr, covDerivRiemann, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, curv_apply g U hg x hx,
    conn, hd, Finset.sum_sub_distrib]
  simp_rw [christoffel_symm g U hg x hx _ a e,
    christoffel_symm g U hg x hx m _ e]
  simp_rw [mul_comm (riemann g x m _ b c)]
  ring

private lemma cr_skew {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e b c : Fin D) :
    (cr g x e b c)ᵀ * g x + g x * cr g x e b c = 0 := by
  classical
  have h := parallel_skew g (curv g b c) U hg (smooth_curv g U hg b c)
    (fun y hy => curvature_metric_skew g U hg y hy b c) x hx e
  rw [cr_formula g U hg x hx]
  simp only [Matrix.transpose_sub, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  have hs (B : Fin D → Matrix (Fin D) (Fin D) ℝ) (f : Fin D → ℝ)
      (hb : ∀ s, (B s)ᵀ * g x + g x * B s = 0) :
      (∑ s, f s • (B s)ᵀ * g x) + (∑ s, f s • (g x * B s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s _
    rw [Matrix.smul_mul, ← smul_add, hb s, smul_zero]
  have h1 := hs (fun s => curv g s c x) (fun s => christoffel g x s e b)
    (fun s => curvature_metric_skew g U hg x hx s c)
  have h2 := hs (fun s => curv g b s x) (fun s => christoffel g x s e c)
    (fun s => curvature_metric_skew g U hg x hx b s)
  dsimp only at h
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub] at h
  have hz := congrArg₂ (fun a b : Matrix (Fin D) (Fin D) ℝ => a - b)
    h (congrArg₂ (· + ·) h1 h2)
  simp only [zero_add, sub_zero, Matrix.smul_mul] at hz
  convert hz using 1; abel

private lemma covricci_trace {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e a c : Fin D) :
    (∑ m, covDerivRiemann g x e m a m c) = covDeriv2 g (ricci g) x e a c := by
  classical
  have hd : partialDeriv e (fun y => ricci g y a c) x =
      ∑ m, partialDeriv e (fun y => riemann g y m a m c) x := by
    unfold partialDeriv ricci
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun m y => riemann g y m a m c)
      (fun m _ => (smooth_riemann g U hg m a m c).differentiableOn (by simp) x hx
        |>.differentiableAt (hg.isOpen.mem_nhds hx))]
    simp only [sum_apply]
  rw [covDeriv2, hd]
  simp only [covDerivRiemann, ricci, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  have hcancel : (∑ m, ∑ s, christoffel g x m e s * riemann g x s a m c) =
      ∑ m, ∑ s, christoffel g x s e m * riemann g x m a s c := Finset.sum_comm
  rw [hcancel]
  rw [Finset.sum_comm (f := fun m s => christoffel g x s e a * riemann g x m s m c),
    Finset.sum_comm (f := fun m s => christoffel g x s e c * riemann g x m a m s)]
  ring

private lemma riemann_skew {D : ℕ} (g : Tensor2 D) (x : Coord D) (m a b c : Fin D) :
    riemann g x m a b c = -riemann g x m a c b := by
  classical
  simp only [riemann, Finset.sum_sub_distrib]
  ring

private lemma cr_last_skew {D : ℕ} (g : Tensor2 D) (x : Coord D) (e m a b c : Fin D) :
    covDerivRiemann g x e m a b c = -covDerivRiemann g x e m a c b := by
  have hd : partialDeriv e (fun y => riemann g y m a b c) x =
      -partialDeriv e (fun y => riemann g y m a c b) x := by
    simp_rw [riemann_skew g _ m a b c]
    simp [partialDeriv, fderiv_fun_neg]
  simp only [covDerivRiemann, hd]
  simp_rw [riemann_skew g x _ a b c, riemann_skew g x m _ b c,
    riemann_skew g x m a _ c, riemann_skew g x m a b _]
  simp only [mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

private lemma skew_contraction {D : ℕ} (G : Matrix (Fin D) (Fin D) ℝ)
    (hG : IsUnit G.det) (A : Fin D → Matrix (Fin D) (Fin D) ℝ)
    (hA : ∀ c, (A c)ᵀ * G + G * A c = 0) (m : Fin D) :
    (∑ a, ∑ c, G⁻¹ a c * A c m a) =
      -(∑ s, G⁻¹ m s * (∑ c, A c c s)) := by
  classical
  have hi := Matrix.mul_nonsing_inv G hG
  have hi' := Matrix.nonsing_inv_mul G hG
  have hp (c : Fin D) : A c * G⁻¹ = -(G⁻¹ * (A c)ᵀ) := by
    have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => G⁻¹ * M * G⁻¹) (hA c)
    have he : G⁻¹ * ((A c)ᵀ * G + G * A c) * G⁻¹ =
        G⁻¹ * (A c)ᵀ + A c * G⁻¹ := by
      rw [Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, hi, Matrix.mul_one]
      rw [← Matrix.mul_assoc G⁻¹ G, hi', Matrix.one_mul]
    rw [he, Matrix.mul_zero, Matrix.zero_mul] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [Finset.sum_comm]
  calc
    _ = ∑ c, (A c * G⁻¹) m c := by
      apply Finset.sum_congr rfl
      intro c _
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = -(∑ c, ∑ s, G⁻¹ m s * A c c s) := by
      simp_rw [hp]
      simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_neg_distrib]
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

private lemma md_inv {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e : Fin D) :
    md e (invMetric g) x =
      -(conn g e x * invMetric g x + invMetric g x * (conn g e x)ᵀ) := by
  have hi : g x * invMetric g x = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx))
  have hi' : invMetric g x * g x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx))
  have hgd (i j : Fin D) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.smooth i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hhd (i j : Fin D) : DifferentiableAt ℝ (fun y => invMetric g y i j) x :=
    (smooth_inv g U hg i j).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have he : md e (fun y => invMetric g y * g y) x = 0 := by
    ext i j
    have he : (fun y => (invMetric g y * g y) i j) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix (Fin D) (Fin D) ℝ) i j) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M i j)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hg.nondegenerate y hy)))
    simpa [md, partialDeriv] using
      congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single e 1)) he.fderiv_eq
  rw [md_mul _ _ _ _ hhd hgd, matrix_compat g U hg x hx] at he
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M * invMetric g x) he
  have hex : (md e (invMetric g) x * g x + invMetric g x *
      ((conn g e x)ᵀ * g x + g x * conn g e x)) * invMetric g x =
      md e (invMetric g) x +
        (conn g e x * invMetric g x + invMetric g x * (conn g e x)ᵀ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hi, Matrix.mul_one]
    rw [← Matrix.mul_assoc (invMetric g x) (g x), hi', Matrix.one_mul]
    abel
  rw [hex, Matrix.zero_mul] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma cov2_matrix {D : ℕ} (g F : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e : Fin D) :
    (fun a b => covDeriv2 g F x e a b) =
      md e F x - (conn g e x)ᵀ * F x - F x * conn g e x := by
  classical
  ext a b
  simp only [covDeriv2, md, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    conn, Finset.sum_add_distrib]
  simp_rw [christoffel_symm g U hg x hx _ _ e]
  simp_rw [mul_comm (F x a _)]
  ring

private lemma trace_contract {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℝ) :
    (∑ a, ∑ b, A a b * B a b) = Matrix.trace (A * Bᵀ) := by
  rfl

private lemma trace_derivative {D : ℕ} (g F : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (hF : ∀ i j, ContDiffOn ℝ ∞ (fun x => F x i j) U)
    (x : Coord D) (hx : x ∈ U) (e : Fin D) :
    partialDeriv e (fun y => ∑ a, ∑ b, invMetric g y a b * F y a b) x =
      ∑ a, ∑ b, invMetric g x a b * covDeriv2 g F x e a b := by
  classical
  have hfd (i j : Fin D) : DifferentiableAt ℝ (fun y => F y i j) x :=
    (hF i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hhd (i j : Fin D) : DifferentiableAt ℝ (fun y => invMetric g y i j) x :=
    (smooth_inv g U hg i j).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have hd : partialDeriv e (fun y => ∑ a, ∑ b, invMetric g y a b * F y a b) x =
      ∑ a, ∑ b, (md e (invMetric g) x a b * F x a b +
        invMetric g x a b * md e F x a b) := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun a y => ∑ b, invMetric g y a b * F y a b)
      (fun a _ => DifferentiableAt.fun_sum fun b _ => (hhd a b).mul (hfd a b))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun b y => invMetric g y a b * F y a b)
      (fun b _ => (hhd a b).mul (hfd a b))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [fderiv_fun_mul (hhd a b) (hfd a b)]
    simp [md, partialDeriv, smul_eq_mul, mul_comm, add_comm]
  rw [hd]
  simp only [Finset.sum_add_distrib]
  rw [trace_contract (md e (invMetric g) x) (F x),
    trace_contract (invMetric g x) (md e F x),
    trace_contract (invMetric g x) (fun a b => covDeriv2 g F x e a b)]
  rw [md_inv g U hg x hx, cov2_matrix g F U hg x hx]
  simp only [Matrix.neg_mul, Matrix.add_mul, Matrix.trace_neg, Matrix.trace_add,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle (conn g e x) (invMetric g x) (F x)ᵀ,
    Matrix.trace_mul_cycle (F x)ᵀ (conn g e x) (invMetric g x)]
  simp only [Matrix.mul_assoc]
  ring

private lemma covricci_symm {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e a b : Fin D) :
    covDeriv2 g (ricci g) x e a b = covDeriv2 g (ricci g) x e b a := by
  have hr (y : Coord D) (hy : y ∈ U) (i j : Fin D) : ricci g y i j = ricci g y j i := by
    have h := einsteinTensor_symm g U hg y hy i j
    simp only [einsteinTensor, hg.symm y hy i j] at h
    linarith
  have hd : partialDeriv e (fun y => ricci g y a b) x =
      partialDeriv e (fun y => ricci g y b a) x := by
    have he : (fun y => ricci g y a b) =ᶠ[𝓝 x] (fun y => ricci g y b a) := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      exact hr y hy a b
    exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single e 1)) he.fderiv_eq
  simp only [covDeriv2, hd, hr x hx]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma inv_symm {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (a b : Fin D) :
    invMetric g x a b = invMetric g x b a := by
  have ht : (g x)ᵀ = g x := by
    ext i j
    exact hg.symm x hx j i
  have h : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by rw [Matrix.transpose_nonsing_inv, ht]
  exact congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M b a) h

private lemma contracted_bianchi {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e : Fin D) :
    partialDeriv e (scalarCurvature g) x = 2 * divergence g (ricci g) x e := by
  classical
  have hfirst (a c : Fin D) : covDeriv2 g (ricci g) x e a c +
      (∑ m, covDerivRiemann g x m m a c e) - covDeriv2 g (ricci g) x c a e = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ)
      (fun m _ => differential_bianchi_identity g U hg x hx e m a m c)
    simp only [Finset.sum_add_distrib] at h
    simp_rw [cr_last_skew g x c _ a e _, Finset.sum_neg_distrib] at h
    rw [covricci_trace g U hg x hx, covricci_trace g U hg x hx] at h
    linarith
  have hsk (m : Fin D) : (∑ a, ∑ c, invMetric g x a c * covDerivRiemann g x m m a c e) =
      -(∑ s, invMetric g x m s * covDeriv2 g (ricci g) x m s e) := by
    have h := skew_contraction (g x) (isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx))
      (fun c => cr g x m c e) (fun c => cr_skew g U hg x hx m c e) m
    simpa only [cr, invMetric, ← covricci_trace g U hg x hx] using h
  have hcurv : (∑ a, ∑ c, invMetric g x a c *
      (∑ m, covDerivRiemann g x m m a c e)) = -divergence g (ricci g) x e := by
    calc
      _ = ∑ m, ∑ a, ∑ c, invMetric g x a c * covDerivRiemann g x m m a c e := by
        simp only [Finset.mul_sum]
        calc
          _ = ∑ a, ∑ m, ∑ c, invMetric g x a c * covDerivRiemann g x m m a c e := by
            apply Finset.sum_congr rfl
            intro a _
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ = -(∑ m, ∑ s, invMetric g x m s * covDeriv2 g (ricci g) x m s e) := by
        simp_rw [hsk, Finset.sum_neg_distrib]
      _ = _ := by
        unfold divergence
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro l _
        rw [inv_symm g U hg x hx l b, covricci_symm g U hg x hx l b e]
  have hdiv : (∑ a, ∑ c, invMetric g x a c * covDeriv2 g (ricci g) x c a e) =
      divergence g (ricci g) x e := by
    unfold divergence
    simp_rw [covricci_symm g U hg x hx _ _ e]
  have h : (∑ a, ∑ c, invMetric g x a c *
      (covDeriv2 g (ricci g) x e a c + (∑ m, covDerivRiemann g x m m a c e) -
        covDeriv2 g (ricci g) x c a e)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro c _
    rw [hfirst a c, mul_zero]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at h
  rw [hcurv, hdiv, ← trace_derivative g (ricci g) U hg (smooth_ricci g U hg) x hx e] at h
  change partialDeriv e (scalarCurvature g) x - divergence g (ricci g) x e -
    divergence g (ricci g) x e = 0 at h
  linarith

private lemma covDeriv_linear {D : ℕ} (g A B : Tensor2 D) (r s : ℝ)
    (x : Coord D) (l a b : Fin D)
    (hA : DifferentiableAt ℝ (fun y => A y a b) x)
    (hB : DifferentiableAt ℝ (fun y => B y a b) x) :
    covDeriv2 g (fun y i j => r * A y i j + s * B y i j) x l a b =
      r * covDeriv2 g A x l a b + s * covDeriv2 g B x l a b := by
  have hd : partialDeriv l (fun y => r * A y a b + s * B y a b) x =
      r * partialDeriv l (fun y => A y a b) x +
      s * partialDeriv l (fun y => B y a b) x := by
    unfold partialDeriv
    have hfun : (fun y : Coord D => r * A y a b + s * B y a b) =
        ((fun y : Coord D => r * A y a b) + (fun y => s * B y a b)) := rfl
    rw [hfun, ((hA.hasFDerivAt.const_mul r).add (hB.hasFDerivAt.const_mul s)).fderiv]
    simp [smul_eq_mul]
  unfold covDeriv2
  rw [hd]
  have hs : (∑ t : Fin D,
      (christoffel g x t l a * (r * A x t b + s * B x t b) +
        christoffel g x t l b * (r * A x a t + s * B x a t))) =
      r * (∑ t : Fin D, (christoffel g x t l a * A x t b +
        christoffel g x t l b * A x a t)) +
      s * (∑ t : Fin D, (christoffel g x t l a * B x t b +
        christoffel g x t l b * B x a t)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hs]
  ring

private lemma divergence_linear {D : ℕ} (g A B : Tensor2 D) (r s : ℝ)
    (x : Coord D) (a : Fin D)
    (hA : ∀ b, DifferentiableAt ℝ (fun y => A y a b) x)
    (hB : ∀ b, DifferentiableAt ℝ (fun y => B y a b) x) :
    divergence g (fun y i j => r * A y i j + s * B y i j) x a =
      r * divergence g A x a + s * divergence g B x a := by
  unfold divergence
  simp_rw [covDeriv_linear g A B r s x _ a _ (hA _) (hB _)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro l _
  ring


private theorem covDeriv2_scalar_mul_at {D : ℕ}
    (g A : Tensor2 D) (f : Coord D → ℝ)
    (x : Coord D) (l a b : Fin D)
    (hf : DifferentiableAt ℝ f x)
    (hA : DifferentiableAt ℝ (fun y => A y a b) x) :
    covDeriv2 g (fun y i j => f y * A y i j) x l a b =
      partialDeriv l f x * A x a b +
        f x * covDeriv2 g A x l a b := by
  classical
  have hprod :
      partialDeriv l (fun y => f y * A y a b) x =
      partialDeriv l f x * A x a b +
        f x * partialDeriv l (fun y => A y a b) x := by
    have hd := fderiv_fun_mul hf hA
    change (fderiv ℝ (fun y => f y * A y a b) x)
      (Pi.single l 1) =
      (fderiv ℝ f x) (Pi.single l 1) * A x a b +
        f x * (fderiv ℝ (fun y => A y a b) x)
          (Pi.single l 1)
    rw [hd]
    simp only [add_apply,
      smul_apply, smul_eq_mul]
    ring
  have hs :
      (∑ s : Fin D,
        (christoffel g x s l a * (f x * A x s b) +
          christoffel g x s l b * (f x * A x a s))) =
      f x * (∑ s : Fin D,
        (christoffel g x s l a * A x s b +
          christoffel g x s l b * A x a s)) := by
    calc
      _ = ∑ s : Fin D,
          f x * (christoffel g x s l a * A x s b +
            christoffel g x s l b * A x a s) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = _ := by simp only [Finset.mul_sum]
  change partialDeriv l (fun y => f y * A y a b) x -
      (∑ s : Fin D, (christoffel g x s l a * (f x * A x s b) +
        christoffel g x s l b * (f x * A x a s))) =
      partialDeriv l f x * A x a b +
      f x * (partialDeriv l (fun y => A y a b) x -
        (∑ s : Fin D, (christoffel g x s l a * A x s b +
          christoffel g x s l b * A x a s)))
  rw [hprod, hs]
  ring

private theorem metric_contract_derivative {D : ℕ}
    (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U)
    (f : Coord D → ℝ) (a : Fin D) :
    (∑ b : Fin D, ∑ l : Fin D,
      invMetric g x b l * (partialDeriv l f x * g x a b)) =
      partialDeriv a f x := by
  classical
  have hmat : Matrix.transpose (g x) = g x := by
    ext i j
    exact hg.symm x hx j i
  have hinvSymm : Matrix.transpose ((g x)⁻¹) = (g x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hmat]
  have hinvSymmComp (i j : Fin D) :
      (g x)⁻¹ i j = (g x)⁻¹ j i := by
    have hh := congrArg (fun A : Matrix (Fin D) (Fin D) ℝ => A j i) hinvSymm
    simpa [Matrix.transpose_apply] using hh
  have hdet : IsUnit (g x).det :=
    isUnit_iff_ne_zero.mpr (hg.nondegenerate x hx)
  have hmulinverse : (g x)⁻¹ * g x =
      (1 : Matrix (Fin D) (Fin D) ℝ) :=
    Matrix.nonsing_inv_mul (g x) hdet
  have hInv (t j : Fin D) :
      (∑ b : Fin D, invMetric g x b t * g x b j) =
        if t = j then (1 : ℝ) else 0 := by
    calc
      _ = ∑ b : Fin D, (g x)⁻¹ t b * g x b j := by
        apply Finset.sum_congr rfl
        intro b _
        change (g x)⁻¹ b t * g x b j =
          (g x)⁻¹ t b * g x b j
        rw [hinvSymmComp b t]
      _ = ((g x)⁻¹ * g x) t j := by rw [Matrix.mul_apply]
      _ = (1 : Matrix (Fin D) (Fin D) ℝ) t j := by rw [hmulinverse]
      _ = _ := by simp [Matrix.one_apply]
  calc
    _ = ∑ l : Fin D, ∑ b : Fin D,
          invMetric g x b l * (partialDeriv l f x * g x a b) :=
            Finset.sum_comm
    _ = ∑ l : Fin D, ∑ b : Fin D,
          (invMetric g x b l * g x b a) * partialDeriv l f x := by
            apply Finset.sum_congr rfl
            intro l _
            apply Finset.sum_congr rfl
            intro b _
            rw [hg.symm x hx a b]
            ring
    _ = ∑ l : Fin D,
          (∑ b : Fin D, invMetric g x b l * g x b a) *
            partialDeriv l f x := by
              simp only [Finset.sum_mul]
    _ = ∑ l : Fin D,
          (if l = a then (1 : ℝ) else 0) *
            partialDeriv l f x := by
              simp_rw [hInv]
    _ = partialDeriv a f x := by simp


private lemma smooth_scalar {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) : ContDiffOn ℝ ∞ (scalarCurvature g) U := by
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
    (smooth_inv g U hg a b).mul (smooth_ricci g U hg a b)

theorem solution {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ a : Fin D, divergence g (einsteinTensor g) x a = 0 := by
  classical
  intro x hx a
  have hR : DifferentiableAt ℝ (scalarCurvature g) x :=
    (smooth_scalar g U hg).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have hgd (i j : Fin D) : DifferentiableAt ℝ (fun y => g y i j) x :=
    (hg.smooth i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hrd (i j : Fin D) : DifferentiableAt ℝ (fun y => ricci g y i j) x :=
    (smooth_ricci g U hg i j).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have he : einsteinTensor g = (fun y i j => 1 * ricci g y i j +
      (-(1/2) : ℝ) * (scalarCurvature g y * g y i j)) := by
    funext y i j
    simp only [einsteinTensor]
    ring
  rw [he, divergence_linear g (ricci g) (fun y i j => scalarCurvature g y * g y i j)
    1 (-(1/2)) x a (hrd a) (fun b => hR.mul (hgd a b))]
  have hs : divergence g (fun y i j => scalarCurvature g y * g y i j) x a =
      partialDeriv a (scalarCurvature g) x := by
    unfold divergence
    simp_rw [covDeriv2_scalar_mul_at g g (scalarCurvature g) x _ a _ hR (hgd a _),
      metric_covariantly_constant g U hg x hx, mul_zero, add_zero]
    exact metric_contract_derivative g U hg x hx _ a
  rw [hs, contracted_bianchi g U hg x hx a]
  ring
