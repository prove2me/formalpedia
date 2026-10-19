-- Prove2me | solution 1 for EinsteinFieldEquationsD.differential_bianchi_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:39:45.496338+00:00
-- url     : https://prove2.me/submissions/78dd3098-eed5-4944-a991-9c8c520c7e1a

import Definitions.Def_EinsteinFieldEquationsD_Defs

open EinsteinFieldEquationsD
open scoped Topology ContDiff

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

private lemma md_sub {D : ℕ} (a : Fin D) (F G : Tensor2 D) (x : Coord D)
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) :
    md a (F - G) x = md a F x - md a G x := by
  ext i j
  exact congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single a 1))
    ((hF i j).hasFDerivAt.sub (hG i j).hasFDerivAt).fderiv

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

private lemma smooth_md {D : ℕ} (F : Tensor2 D) (U : Set (Coord D))
    (hU : IsOpen U) (hF : ∀ i j, ContDiffOn ℝ ∞ (fun y => F y i j) U) (a i j : Fin D) :
    ContDiffOn ℝ ∞ (fun y => md a F y i j) U :=
  smooth_partial _ U hU (hF i j) a

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

private lemma md_curv {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e b c : Fin D) :
    md e (curv g b c) x =
      md e (md b (conn g c)) x - md e (md c (conn g b)) x +
        md e (conn g b) x * conn g c x + conn g b x * md e (conn g c) x -
        md e (conn g c) x * conn g b x - conn g c x * md e (conn g b) x := by
  classical
  have hA (k i j : Fin D) : DifferentiableAt ℝ (fun y => conn g k y i j) x :=
    (smooth_christoffel g U hg i j k).differentiableOn (by simp) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx)
  have hB (k l i j : Fin D) : DifferentiableAt ℝ (fun y => md k (conn g l) y i j) x :=
    (smooth_md (conn g l) U hg.isOpen (fun i j => smooth_christoffel g U hg i j l)
      k i j).differentiableOn (by simp) x hx |>.differentiableAt (hg.isOpen.mem_nhds hx)
  have hP (k l i j : Fin D) : DifferentiableAt ℝ (fun y => (conn g k y * conn g l y) i j) x :=
    by
      change DifferentiableAt ℝ (fun y => ∑ s, conn g k y i s * conn g l y s j) x
      exact DifferentiableAt.fun_sum (u := Finset.univ)
        (A := fun s y => conn g k y i s * conn g l y s j) fun s _ => (hA k i s).mul (hA l s j)
  rw [curv, md_sub e
      (md b (conn g c) - md c (conn g b) + (fun y => conn g b y * conn g c y))
      (fun y => conn g c y * conn g b y) x
      (fun i j => ((hB b c i j).sub (hB c b i j)).add (hP b c i j)) (hP c b),
    md_add e (md b (conn g c) - md c (conn g b)) (fun y => conn g b y * conn g c y) x
      (fun i j => (hB b c i j).sub (hB c b i j)) (hP b c),
    md_sub e (md b (conn g c)) (md c (conn g b)) x (hB b c) (hB c b),
    md_mul e (conn g b) (conn g c) x (hA b) (hA c),
    md_mul e (conn g c) (conn g b) x (hA c) (hA b)]
  abel

private lemma matrix_bianchi {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e b c : Fin D) :
    (md e (curv g b c) x + conn g e x * curv g b c x - curv g b c x * conn g e x) +
    (md b (curv g c e) x + conn g b x * curv g c e x - curv g c e x * conn g b x) +
    (md c (curv g e b) x + conn g c x * curv g e b x - curv g e b x * conn g c x) = 0 := by
  have hc (a b c : Fin D) : md a (md b (conn g c)) x = md b (md a (conn g c)) x := by
    ext i j
    exact partial_comm _ U hg.isOpen (smooth_christoffel g U hg i j c) x hx a b
  rw [md_curv g U hg x hx, md_curv g U hg x hx, md_curv g U hg x hx]
  rw [hc e b c, hc c e b, hc b c e]
  simp only [curv, Pi.sub_apply, Pi.add_apply]
  noncomm_ring

private lemma riemann_skew {D : ℕ} (g : Tensor2 D) (x : Coord D) (m a b c : Fin D) :
    riemann g x m a b c = -riemann g x m a c b := by
  classical
  simp only [riemann, Finset.sum_sub_distrib]
  ring

private lemma covDeriv_decomp {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) (e m a b c : Fin D) :
    covDerivRiemann g x e m a b c =
      (md e (curv g b c) x + conn g e x * curv g b c x -
        curv g b c x * conn g e x) m a -
      ∑ s, (christoffel g x s e b * riemann g x m a s c +
        christoffel g x s e c * riemann g x m a b s) := by
  classical
  have he : (fun y => riemann g y m a b c) =ᶠ[𝓝 x] (fun y => curv g b c y m a) := by
    filter_upwards [hg.isOpen.mem_nhds hx] with y hy
    exact (curv_apply g U hg y hy m a b c).symm
  have hd : partialDeriv e (fun y => riemann g y m a b c) x =
      md e (curv g b c) x m a :=
    congrArg (fun L : Coord D →L[ℝ] ℝ => L (Pi.single e 1)) he.fderiv_eq
  simp only [covDerivRiemann, hd, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  simp_rw [curv_apply g U hg x hx]
  simp only [conn, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [christoffel_symm g U hg x hx m e, christoffel_symm g U hg x hx _ e a]
  rw [show (∑ s, riemann g x m s b c * christoffel g x s a e) =
      ∑ s, christoffel g x s a e * riemann g x m s b c from
    Finset.sum_congr rfl (fun s _ => mul_comm _ _)]
  ring

theorem solution {D : ℕ} (g : Tensor2 D) (U : Set (Coord D)) (hg : IsMetricOn g U) :
    ∀ x ∈ U, ∀ e m a b c : Fin D,
      covDerivRiemann g x e m a b c + covDerivRiemann g x b m a c e
        + covDerivRiemann g x c m a e b = 0 := by
  classical
  intro x hx e m a b c
  have hmat := congrArg (fun M : Matrix (Fin D) (Fin D) ℝ => M m a)
    (matrix_bianchi g U hg x hx e b c)
  simp only [Matrix.add_apply, Matrix.zero_apply] at hmat
  have hcancel :
      (∑ s, (christoffel g x s e b * riemann g x m a s c +
        christoffel g x s e c * riemann g x m a b s)) +
      (∑ s, (christoffel g x s b c * riemann g x m a s e +
        christoffel g x s b e * riemann g x m a c s)) +
      (∑ s, (christoffel g x s c e * riemann g x m a s b +
        christoffel g x s c b * riemann g x m a e s)) = 0 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro s _
    rw [christoffel_symm g U hg x hx s b e,
      christoffel_symm g U hg x hx s c e, christoffel_symm g U hg x hx s c b,
      riemann_skew g x m a c s, riemann_skew g x m a s b, riemann_skew g x m a e s]
    ring
  rw [covDeriv_decomp g U hg x hx, covDeriv_decomp g U hg x hx,
    covDeriv_decomp g U hg x hx]
  linarith
