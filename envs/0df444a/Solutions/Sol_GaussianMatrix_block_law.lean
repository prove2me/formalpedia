-- Prove2me | solution 1 for GaussianMatrix.block_law
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:18:25.357349+00:00
-- url     : https://prove2.me/submissions/37768c48-acce-4d7a-b27e-d1b197bc820f

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_rotation_invariance

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.BlockAux

/-- Columns of a matrix as vectors of Euclidean space. -/
noncomputable def col {n : ℕ} {ι : Type*} (V : Matrix (Fin n) ι ℝ) (j : ι) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => V i j)

lemma col_orthonormal {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin n) ι ℝ) (hV : Vᵀ * V = 1) : Orthonormal ℝ (col V) := by
  rw [orthonormal_iff_ite]
  intro a b
  have := congrFun (congrFun hV b) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
  simp only [col, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [this]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

lemma card_le_of_orthonormal {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin n) ι ℝ) (hV : Vᵀ * V = 1) : Fintype.card ι ≤ n := by
  have := (col_orthonormal V hV).linearIndependent.fintype_card_le_finrank
  simpa [finrank_euclideanSpace] using this

lemma exists_orthogonal_completion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin n) ι ℝ) (hV : Vᵀ * V = 1) (e : ι ↪ Fin n) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, Wᵀ * W = 1 ∧ ∀ i j, W i (e j) = V i j := by
  classical
  let v : Fin n → EuclideanSpace ℝ (Fin n) := Function.extend e (col V) 0
  have hv : Orthonormal ℝ ((Set.range e).domRestrict v) := by
    have h1 : (Set.range e).domRestrict v = col V ∘ (Equiv.ofInjective e e.injective).symm := by
      funext x
      obtain ⟨a, j, rfl⟩ := x
      have : (Equiv.ofInjective e e.injective).symm ⟨e j, j, rfl⟩ = j :=
        (Equiv.ofInjective e e.injective).symm_apply_eq.mpr rfl
      simp only [Set.domRestrict_apply, Function.comp_apply, this, v]
      exact e.injective.extend_apply _ _ _
    rw [h1]
    exact (col_orthonormal V hV).comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])
  refine ⟨Matrix.of fun i a => b a i, ?_, ?_⟩
  · ext a c
    have := (orthonormal_iff_ite.mp b.orthonormal) c a
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [show (if a = c then (1:ℝ) else 0) = if c = a then 1 else 0 by simp [eq_comm], ← this]
  · intro i j
    simp only [Matrix.of_apply]
    rw [hb (e j) ⟨j, rfl⟩]
    simp only [v, e.injective.extend_apply, col]

/-- Restricting the coordinates of an i.i.d. product measure along an injection gives the
product measure on the smaller index set. -/
lemma map_comp_injective_pi {ι κ β : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (e : ι → κ) (he : Function.Injective e) :
    Measure.map (fun x : κ → β => fun j => x (e j)) (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : ι => ν := by
  have hind : iIndepFun (fun (i : κ) (x : κ → β) => x i) (Measure.pi fun _ : κ => ν) :=
    iIndepFun_pi (X := fun _ (y : β) => y) (fun _ => aemeasurable_id)
  have hind' := hind.precomp he
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)]
    at hind'
  rw [hind']
  congr 1
  funext j
  exact (measurePreserving_eval (fun _ : κ => ν) (e j)).map_eq

end GaussianMatrix.BlockAux

open GaussianMatrix GaussianMatrix.BlockAux

theorem solution {n k t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    Measure.map (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (gaussianMatrix n t) = gaussianMatrix k t := by
  classical
  have hk : Fintype.card (Fin k) ≤ Fintype.card (Fin n) := by
    simpa using card_le_of_orthonormal V₁ hV₁
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_orthogonal_completion V₁ hV₁ e
  let H : (Fin n → Fin t → ℝ) → (Fin n → Fin t → ℝ) :=
    fun G => Matrix.of.symm (Wᵀ * Matrix.of G * (1 : Matrix (Fin t) (Fin t) ℝ))
  have hHm : Measurable H := by
    have : H = fun G a l => ∑ i, W i a * G i l := by
      funext G a l; simp [H, Matrix.mul_apply, Matrix.mul_one]
    rw [this]; fun_prop
  have hH : Measure.map H (gaussianMatrix n t) = gaussianMatrix n t :=
    rotation_invariance Wᵀ 1 (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW)
      (by simp)
  have hfun : (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G)) =
      (fun X : Fin n → Fin t → ℝ => fun j => X (e j)) ∘ H := by
    funext G j l
    simp [H, Matrix.mul_apply, hWe]
  rw [hfun, ← Measure.map_map (by fun_prop) hHm, hH]
  exact map_comp_injective_pi _ e e.injective
