-- Prove2me | solution 1 for GaussianMatrix.regression_residual_indep
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:33:42.817489+00:00
-- url     : https://prove2.me/submissions/edfc497e-b785-4809-b71a-c7089ffc2292

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma rri_inner {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma rri_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  have h1 : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.rank] at h
  simp only [Module.finrank_fin_fun] at h2
  omega

lemma rri_exists_V {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    ∃ V : Matrix (Fin k) (Fin (k - n)) ℝ, Vᵀ * V = 1 ∧
      (∀ j : Fin (k - n), H *ᵥ (fun l => V l j) = 0) ∧ ∀ g : Fin k → ℝ,
      g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) = ∑ j, (Vᵀ *ᵥ g) j ^ 2 := by
  set E := EuclideanSpace ℝ (Fin k)
  set T : E →ₗ[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin H).comp (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap with hT
  set K : Submodule ℝ E := LinearMap.ker T with hK
  have hrange : LinearMap.range T = ⊤ := by
    rw [hT, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hH
  have hfin : Module.finrank ℝ K = k - n := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_euclideanSpace_fin] at h
    rw [hK]; omega
  set b : OrthonormalBasis (Fin (k - n)) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hfin)
  set V : Matrix (Fin k) (Fin (k - n)) ℝ := Matrix.of fun l j => ((b j : K) : E).ofLp l with hV
  have hbK : ∀ j, H *ᵥ ((b j : K) : E).ofLp = 0 := by
    intro j
    have : T ((b j : K) : E) = 0 := LinearMap.mem_ker.mp (b j).2
    exact this
  have hVcol : ∀ (j : Fin (k - n)) (g : Fin k → ℝ), (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ g := by
    intro j g; simp [hV, Matrix.mulVec, dotProduct]
  refine ⟨V, ?_, fun j => hbK j, ?_⟩
  · ext j j'
    have h1 : (Vᵀ * V) j j' = inner ℝ ((b j : K) : E) ((b j' : K) : E) := by
      rw [rri_inner]; simp [hV, Matrix.mul_apply, dotProduct]
    rw [h1, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]
  · intro g
    set M := H * Hᵀ with hM
    have hdet : IsUnit M.det := by
      refine isUnit_iff_ne_zero.mpr (rri_det_ne_zero_of_rank _ ?_)
      rw [hM, Matrix.rank_self_mul_transpose, hH]
    set c := M⁻¹ *ᵥ (H *ᵥ g) with hc
    set p := Hᵀ *ᵥ c with hp
    set r := g - p with hr
    have hHr : H *ᵥ r = 0 := by
      rw [hr, Matrix.mulVec_sub, hp, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
    have hq : g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c = r ⬝ᵥ r := by
      have h1 : r ⬝ᵥ p = 0 := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hHr, zero_dotProduct]
      have h2 : g ⬝ᵥ p = (H *ᵥ g) ⬝ᵥ c := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      have h3 : r ⬝ᵥ r = r ⬝ᵥ g - r ⬝ᵥ p := by
        rw [← dotProduct_sub]
      rw [h3, h1, hr, sub_dotProduct, dotProduct_comm p g, h2, sub_zero]
    have hcoord : ∀ j, (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j
      rw [hVcol, hr, dotProduct_sub, hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        hbK, zero_dotProduct, sub_zero]
    have hrK : (WithLp.toLp 2 r : E) ∈ K := by
      simpa [hK, hT] using hHr
    set rK : K := ⟨WithLp.toLp 2 r, hrK⟩
    have hpars := b.sum_inner_mul_inner rK rK
    rw [hq]
    simp_rw [hcoord]
    have hrr : inner ℝ rK rK = r ⬝ᵥ r := by
      rw [Submodule.coe_inner, rri_inner]
    have hbj : ∀ j, inner ℝ (b j) rK = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j; rw [Submodule.coe_inner, rri_inner]
    rw [← hrr, ← hpars]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, hbj, sq]


open scoped RealInnerProductSpace in
theorem rri_main {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    IndepFun (fun g : Fin k → ℝ => H *ᵥ g)
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  set P := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hP
  set E := EuclideanSpace ℝ (Fin k)
  obtain ⟨V, hV, hHV, hq⟩ := rri_exists_V H hH
  set hrow : Fin n → E := fun a => WithLp.toLp 2 (H a) with hhrow
  set vcol : Fin (k - n) → E := fun j => WithLp.toLp 2 (fun l => V l j) with hvcol
  have : IsGaussian (P.map (WithLp.toLp 2 : (Fin k → ℝ) → E)) := by
    rw [hP, map_pi_eq_stdGaussian]; infer_instance
  have hlaw : HasGaussianLaw (WithLp.toLp 2 : (Fin k → ℝ) → E) P := IsGaussian.hasGaussianLaw
  set L : E →L[ℝ] (Fin n → ℝ) × (Fin (k - n) → ℝ) :=
    (ContinuousLinearMap.pi fun a => innerSL ℝ (hrow a)).prod
      (ContinuousLinearMap.pi fun j => innerSL ℝ (vcol j)) with hL
  have hpair : HasGaussianLaw (fun g : Fin k → ℝ =>
      ((fun a => ⟪hrow a, WithLp.toLp 2 g⟫), (fun j => ⟪vcol j, WithLp.toLp 2 g⟫))) P := by
    have := hlaw.map_fun L
    simpa [hL] using this
  have hcov : ∀ a j, cov[fun g : Fin k → ℝ => ⟪hrow a, WithLp.toLp 2 g⟫,
      fun g => ⟪vcol j, WithLp.toLp 2 g⟫; P] = 0 := by
    intro a j
    have hm : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → E) := by fun_prop
    have h1 := covariance_map_fun (μ := P) (X := fun x : E => ⟪hrow a, x⟫)
      (Y := fun x : E => ⟪vcol j, x⟫) (by fun_prop) (by fun_prop) hm.aemeasurable
    rw [← h1, hP, map_pi_eq_stdGaussian, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, innerSL_apply_apply, rri_inner]
    have := congrFun (hHV j) a
    simpa [hhrow, hvcol, Matrix.mulVec, dotProduct] using this
  have hind := hpair.indepFun_of_covariance_eval hcov
  have h1 : (fun g : Fin k → ℝ => fun a => ⟪hrow a, WithLp.toLp 2 g⟫) = fun g => H *ᵥ g := by
    funext g a
    rw [rri_inner]; rfl
  have h2 : (fun g : Fin k → ℝ => fun j => ⟪vcol j, WithLp.toLp 2 g⟫) = fun g => Vᵀ *ᵥ g := by
    funext g j
    rw [rri_inner]; rfl
  rw [h1, h2] at hind
  have hS : Measurable (fun y : Fin (k - n) → ℝ => ∑ j, y j ^ 2) := by fun_prop
  have := hind.comp measurable_id hS
  have h3 : (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      = (fun y : Fin (k - n) → ℝ => ∑ j, y j ^ 2) ∘ (fun g => Vᵀ *ᵥ g) := funext hq
  rw [h3]
  exact this

end GaussianMatrix

open GaussianMatrix

theorem solution {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    IndepFun (fun g : Fin k → ℝ => H *ᵥ g)
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
  rri_main H hH
