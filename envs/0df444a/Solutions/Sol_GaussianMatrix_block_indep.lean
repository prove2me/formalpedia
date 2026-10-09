-- Prove2me | solution 1 for GaussianMatrix.block_indep
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:14:13.133813+00:00
-- url     : https://prove2.me/submissions/9418f723-65a1-429b-8ea1-fa013f81a1b7

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

theorem solution {n k r t : ℕ} (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin r) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1) (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G))
      (fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₂ᵀ * Matrix.of G)) (gaussianMatrix n t) := by
  classical
  -- the concatenated matrix `[V₁ V₂]` has orthonormal columns
  let V : Matrix (Fin n) (Fin k ⊕ Fin r) ℝ := Matrix.fromCols V₁ V₂
  have hV₂₁ : V₂ᵀ * V₁ = 0 := by
    rw [← Matrix.transpose_transpose V₁, ← Matrix.transpose_mul, hV₁₂, Matrix.transpose_zero]
  have hV : Vᵀ * V = 1 := by
    simp only [V, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hV₁, hV₂, hV₁₂, hV₂₁,
      Matrix.fromBlocks_one]
  have hk : Fintype.card (Fin k ⊕ Fin r) ≤ Fintype.card (Fin n) := by
    simpa using card_le_of_orthonormal V hV
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  obtain ⟨W, hW, hWe⟩ := exists_orthogonal_completion V hV e
  let H : (Fin n → Fin t → ℝ) → (Fin n → Fin t → ℝ) :=
    fun G => Matrix.of.symm (Wᵀ * Matrix.of G * (1 : Matrix (Fin t) (Fin t) ℝ))
  have hHm : Measurable H := by
    have : H = fun G a l => ∑ i, W i a * G i l := by
      funext G a l; simp [H, Matrix.mul_apply, Matrix.mul_one]
    rw [this]; fun_prop
  have hH : Measure.map H (gaussianMatrix n t) = gaussianMatrix n t :=
    rotation_invariance Wᵀ 1 (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hW)
      (by simp)
  -- the rows of `H G` are independent under the Gaussian law
  have hmeas : ∀ a, Measurable fun G => H G a := fun a => (measurable_pi_apply a).comp hHm
  have hind : iIndepFun (fun (a : Fin n) G => H G a) (gaussianMatrix n t) := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => (hmeas a).aemeasurable)]
    have h1 : ∀ a, Measure.map (fun G => H G a) (gaussianMatrix n t) =
        Measure.pi fun _ : Fin t => gaussianReal 0 1 := by
      intro a
      rw [show (fun G => H G a) = (fun f => f a) ∘ H from rfl,
        ← Measure.map_map (measurable_pi_apply a) hHm, hH]
      exact (measurePreserving_eval (fun _ : Fin n => Measure.pi fun _ : Fin t => gaussianReal 0 1)
        a).map_eq
    simp_rw [h1]
    exact hH
  let S : Finset (Fin n) := Finset.univ.map (Function.Embedding.inl.trans e)
  let T : Finset (Fin n) := Finset.univ.map (Function.Embedding.inr.trans e)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [S, T, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, hj⟩ := hb
    exact absurd (e.injective hj) (by simp)
  have hpair := hind.indepFun_finset S T hST hmeas
  have hS : ∀ j : Fin k, e (Sum.inl j) ∈ S := fun j => by simp [S]
  have hT : ∀ j : Fin r, e (Sum.inr j) ∈ T := fun j => by simp [T]
  let φ : (S → Fin t → ℝ) → (Fin k → Fin t → ℝ) := fun y j => y ⟨e (Sum.inl j), hS j⟩
  let ψ : (T → Fin t → ℝ) → (Fin r → Fin t → ℝ) := fun y j => y ⟨e (Sum.inr j), hT j⟩
  have hφ : Measurable φ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hψ : Measurable ψ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have h := hpair.comp hφ hψ
  convert h using 1
  · funext G j l
    simp [φ, H, Matrix.mul_apply, hWe, V]
  · funext G j l
    simp [ψ, H, Matrix.mul_apply, hWe, V]
