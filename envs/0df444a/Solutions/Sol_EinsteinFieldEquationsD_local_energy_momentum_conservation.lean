-- Prove2me | solution 1 for EinsteinFieldEquationsD.local_energy_momentum_conservation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:29:42.672037+00:00
-- url     : https://prove2.me/submissions/4b08c815-3bfd-4286-90c8-2129db1c68de

import Theorems.Thm_EinsteinFieldEquationsD_einsteinTensor_divergence_free
import Theorems.Thm_EinsteinFieldEquationsD_metric_covariantly_constant

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

private lemma smooth_riemann {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (m a b c : Fin D) :
    ContDiffOn ℝ ∞ (fun x => riemann g x m a b c) U := by
  unfold riemann
  apply ContDiffOn.add
  · exact (smooth_partial _ U hg.isOpen (smooth_christoffel g U hg m a c) b).sub
      (smooth_partial _ U hg.isOpen (smooth_christoffel g U hg m a b) c)
  · exact ContDiffOn.sum fun s _ =>
      ((smooth_christoffel g U hg m s b).mul (smooth_christoffel g U hg s c a)).sub
      ((smooth_christoffel g U hg m s c).mul (smooth_christoffel g U hg s b a))

private lemma smooth_einstein {D : ℕ} (g : Tensor2 D) (U : Set (Coord D))
    (hg : IsMetricOn g U) (a b : Fin D) :
    ContDiffOn ℝ ∞ (fun x => einsteinTensor g x a b) U := by
  have hRic (i j : Fin D) : ContDiffOn ℝ ∞ (fun x => ricci g x i j) U :=
    ContDiffOn.sum fun c _ => smooth_riemann g U hg c i c j
  have hSc : ContDiffOn ℝ ∞ (scalarCurvature g) U :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (smooth_inv g U hg i j).mul (hRic i j)
  exact (hRic a b).sub ((contDiffOn_const.mul hSc).mul (hg.smooth a b))

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

private lemma divergence_local {D : ℕ} (g A B : Tensor2 D) (U : Set (Coord D))
    (hU : IsOpen U) (h : ∀ y ∈ U, ∀ a b, A y a b = B y a b)
    (x : Coord D) (hx : x ∈ U) (a : Fin D) :
    divergence g A x a = divergence g B x a := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro l _
  have he : (fun y => A y a b) =ᶠ[𝓝 x] (fun y => B y a b) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact h y hy a b
  have hd := congrArg (fun F : Coord D →L[ℝ] ℝ => F (Pi.single l 1)) he.fderiv_eq
  unfold covDeriv2 partialDeriv
  rw [hd]
  simp_rw [h x hx]

theorem solution {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D)) (Λ G c : ℝ)
    (hg : IsMetricOn g U) (hG : 0 < G) (hc : 0 < c)
    (hEFE : EinsteinFieldEquationsOn g T Λ (einsteinGravitationalConstant G c) U) :
    ∀ x ∈ U, ∀ a : Fin D, divergence g T x a = 0 := by
  let κ := einsteinGravitationalConstant G c
  have hκ : κ ≠ 0 := ne_of_gt (by dsimp [κ, einsteinGravitationalConstant]; positivity)
  let A : Tensor2 D := fun y a b => (1 / κ) * einsteinTensor g y a b + (Λ / κ) * g y a b
  have hloc : ∀ y ∈ U, ∀ a b, T y a b = A y a b := by
    intro y hy a b
    have he := hEFE y hy a b
    change einsteinTensor g y a b + Λ * g y a b = κ * T y a b at he
    dsimp [A]
    field_simp
    nlinarith
  intro x hx a
  rw [divergence_local g T A U hg.isOpen hloc x hx a]
  change divergence g (fun y i j => (1 / κ) * einsteinTensor g y i j +
    (Λ / κ) * g y i j) x a = 0
  rw [divergence_linear g (einsteinTensor g) g (1 / κ) (Λ / κ) x a
    (fun b => ((smooth_einstein g U hg a b).differentiableOn (by simp)) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx))
    (fun b => ((hg.smooth a b).differentiableOn (by simp)) x hx |>.differentiableAt
      (hg.isOpen.mem_nhds hx))]
  rw [einsteinTensor_divergence_free g U hg x hx a]
  have hm : divergence g g x a = 0 := by
    simp [divergence, metric_covariantly_constant g U hg x hx]
  rw [hm]
  ring
