-- Prove2me | solution 1 for GaussianMatrix.residual_law
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:46:46.571545+00:00
-- url     : https://prove2.me/submissions/8fc815e3-25e3-4ae5-8bcd-0132a968de50

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_block_law

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- A standard Gaussian vector mapped by `Vᵀ`, with `V` having orthonormal columns, is a
standard Gaussian vector (the case `t = 1` of `block_law`, reshaped). -/
lemma rl_vec_law {m d : ℕ} (V : Matrix (Fin m) (Fin d) ℝ) (hV : Vᵀ * V = 1) :
    Measure.map (fun g : Fin m → ℝ => Vᵀ *ᵥ g) (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  -- column-vector embedding and its inverse
  have hι : ∀ p : ℕ, MeasurePreserving
      (fun (g : Fin p → ℝ) (a : Fin p) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) (gaussianMatrix p 1) := fun p =>
    measurePreserving_pi _ _ fun _ => (measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)).symm
  have hev : ∀ p : ℕ, MeasurePreserving
      (fun (G : Fin p → Fin 1 → ℝ) (a : Fin p) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a))
      (gaussianMatrix p 1) (Measure.pi fun _ : Fin p => gaussianReal 0 1) := fun p =>
    measurePreserving_pi _ _ fun _ => measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)
  have hB := block_law (t := 1) V hV
  have hFm : Measurable (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hfun : (fun g : Fin m → ℝ => Vᵀ *ᵥ g) =
      (fun (G : Fin d → Fin 1 → ℝ) (a : Fin d) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a)) ∘
      (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) ∘
      (fun (g : Fin m → ℝ) (a : Fin m) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a)) := by
    funext g a
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, MeasurableEquiv.funUnique]
  rw [hfun, ← Measure.map_map (hev d).measurable (hFm.comp (hι m).measurable),
    ← Measure.map_map hFm (hι m).measurable, (hι m).map_eq, hB, (hev d).map_eq]

lemma rl_inner {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma rl_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
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

lemma rl_exists_V {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    ∃ V : Matrix (Fin k) (Fin (k - n)) ℝ, Vᵀ * V = 1 ∧ ∀ g : Fin k → ℝ,
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
  refine ⟨V, ?_, ?_⟩
  · ext j j'
    have h1 : (Vᵀ * V) j j' = inner ℝ ((b j : K) : E) ((b j' : K) : E) := by
      rw [rl_inner]; simp [hV, Matrix.mul_apply, dotProduct]
    rw [h1, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]
  · intro g
    set M := H * Hᵀ with hM
    have hdet : IsUnit M.det := by
      refine isUnit_iff_ne_zero.mpr (rl_det_ne_zero_of_rank _ ?_)
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
      rw [Submodule.coe_inner, rl_inner]
    have hbj : ∀ j, inner ℝ (b j) rK = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j; rw [Submodule.coe_inner, rl_inner]
    rw [← hrr, ← hpars]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, hbj, sq]

theorem rl_main {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  obtain ⟨V, hV, hq⟩ := rl_exists_V H hH
  have hfun : (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) =
      (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) ∘ (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := funext hq
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  have hVm : Measurable (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := by
    refine measurable_pi_lambda _ fun a => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [hfun, ← Measure.map_map hS hVm, rl_vec_law V hV]

end GaussianMatrix

open GaussianMatrix

theorem solution {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) :=
  rl_main H hH
