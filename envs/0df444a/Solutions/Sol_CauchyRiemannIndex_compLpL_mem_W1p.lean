-- Prove2me | solution 1 for CauchyRiemannIndex.compLpL_mem_W1p
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T16:08:20.612978+00:00
-- url     : https://prove2.me/submissions/dc79ba4a-8176-4180-ac61-d6fc665c08cb

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Calculus.Deriv.Prod

open Matrix
open MeasureTheory Matrix CauchyRiemannIndex
open scoped ENNReal ContDiff

/-!
# Entrywise algebra of the block-diagonal sum `ConleyZehnder.diamond`
-/


namespace CRIFD

/-- The coordinate equivalence used by `ConleyZehnder.diamond`. -/
abbrev dE (m₁ m₂ : ℕ) :
    ((Fin m₁ ⊕ Fin m₁) ⊕ (Fin m₂ ⊕ Fin m₂)) ≃ (Fin (m₁ + m₂) ⊕ Fin (m₁ + m₂)) :=
  (Equiv.sumSumSumComm (Fin m₁) (Fin m₁) (Fin m₂) (Fin m₂)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

variable {m₁ m₂ : ℕ}

lemma diamond_eq (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond A B = Matrix.reindex (dE m₁ m₂) (dE m₁ m₂) (Matrix.fromBlocks A 0 0 B) :=
  rfl

lemma diamond_apply_dE (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) (a b) :
    ConleyZehnder.diamond A B (dE m₁ m₂ a) (dE m₁ m₂ b) = Matrix.fromBlocks A 0 0 B a b := by
  rw [diamond_eq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- Every entry of `A ⋄ B` is an entry of `A`, an entry of `B`, or `0`, at positions that do not
depend on `A` and `B`. -/
lemma diamond_entry (i j : Fin (m₁ + m₂) ⊕ Fin (m₁ + m₂)) :
    (∃ a b, ∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = A a b) ∨
      (∃ a b, ∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = B a b) ∨
      (∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = 0) := by
  obtain ⟨a, rfl⟩ := (dE m₁ m₂).surjective i
  obtain ⟨b, rfl⟩ := (dE m₁ m₂).surjective j
  rcases a with a | a <;> rcases b with b | b
  · exact Or.inl ⟨a, b, fun A B => by rw [diamond_apply_dE]; rfl⟩
  · exact Or.inr (Or.inr fun A B => by rw [diamond_apply_dE]; rfl)
  · exact Or.inr (Or.inr fun A B => by rw [diamond_apply_dE]; rfl)
  · exact Or.inr (Or.inl ⟨a, b, fun A B => by rw [diamond_apply_dE]; rfl⟩)

lemma continuous_diamond {X : Type*} [TopologicalSpace X] {f : X → CauchyRiemannIndex.Mat m₁}
    {g : X → CauchyRiemannIndex.Mat m₂} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ConleyZehnder.diamond (f x) (g x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · simp only [h]; exact (continuous_apply b).comp ((continuous_apply a).comp hf)
  · simp only [h]; exact (continuous_apply b).comp ((continuous_apply a).comp hg)
  · simp only [h]; exact continuous_const

lemma abs_sub_diamond_le (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : ∀ i j, |A i j - A' i j| ≤ ε) (hB : ∀ i j, |B i j - B' i j| ≤ ε)
    (i j) : |ConleyZehnder.diamond A B i j - ConleyZehnder.diamond A' B' i j| ≤ ε := by
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · rw [h, h]; exact hA a b
  · rw [h, h]; exact hB a b
  · rw [h, h, sub_zero, abs_zero]; exact hε

lemma diamond_mul (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond (A * A') (B * B') =
      ConleyZehnder.diamond A B * ConleyZehnder.diamond A' B' := by
  rw [diamond_eq, diamond_eq, diamond_eq, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

lemma diamond_transpose (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    (ConleyZehnder.diamond A B)ᵀ = ConleyZehnder.diamond Aᵀ Bᵀ := by
  rw [diamond_eq, diamond_eq, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

lemma diamond_one : ConleyZehnder.diamond (1 : CauchyRiemannIndex.Mat m₁)
    (1 : CauchyRiemannIndex.Mat m₂) = 1 := by
  rw [diamond_eq, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

lemma diamond_sub (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond (A - A') (B - B') =
      ConleyZehnder.diamond A B - ConleyZehnder.diamond A' B' := by
  ext i j
  rw [Matrix.sub_apply]
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · rw [h, h, h]; rfl
  · rw [h, h, h]; rfl
  · rw [h, h, h, sub_zero]

lemma det_diamond (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    (ConleyZehnder.diamond A B).det = A.det * B.det := by
  rw [diamond_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma J_eq_diamond :
    CauchyRiemannIndex.J₀ (m₁ + m₂) =
      ConleyZehnder.diamond (CauchyRiemannIndex.J₀ m₁) (CauchyRiemannIndex.J₀ m₂) := by
  ext i j
  obtain ⟨a, rfl⟩ := (dE m₁ m₂).surjective i
  obtain ⟨b, rfl⟩ := (dE m₁ m₂).surjective j
  rw [diamond_apply_dE]
  rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
    simp [Matrix.J, Matrix.one_apply]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

lemma hasDerivAt_mat_iff {m : ℕ} {f : ℝ → CauchyRiemannIndex.Mat m} {f' : CauchyRiemannIndex.Mat m}
    {t : ℝ} : HasDerivAt f f' t ↔ ∀ i j, HasDerivAt (fun s => f s i j) (f' i j) t := by
  constructor
  · intro h i j
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j
  · intro h
    exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

lemma hasDerivAt_diamond {f : ℝ → CauchyRiemannIndex.Mat m₁} {g : ℝ → CauchyRiemannIndex.Mat m₂}
    {f' : CauchyRiemannIndex.Mat m₁} {g' : CauchyRiemannIndex.Mat m₂} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ConleyZehnder.diamond (f s) (g s)) (ConleyZehnder.diamond f' g') t := by
  rw [hasDerivAt_mat_iff] at hf hg ⊢
  intro i j
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · simp only [h]; exact hf a b
  · simp only [h]; exact hg a b
  · simp only [h]; exact hasDerivAt_const _ _

end CRIFD

/-!
# Index additivity of `∂ₛ + J₀ ∂ₜ + S₁ ⋄ S₂`
-/


noncomputable section

namespace CRIFC2

open CRIFD

variable {m₁ m₂ : ℕ}

/-! ### Coordinates of `ℝ^{2(m₁+m₂)} = ℝ^{2m₁} ⊕ ℝ^{2m₂}` -/

/-- First block of coordinates. -/
def pr₁L : Vec (m₁ + m₂) →ₗ[ℝ] Vec m₁ where
  toFun v := WithLp.toLp 2 (fun a => v (dE m₁ m₂ (Sum.inl a)))
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp

/-- Second block of coordinates. -/
def pr₂L : Vec (m₁ + m₂) →ₗ[ℝ] Vec m₂ where
  toFun v := WithLp.toLp 2 (fun a => v (dE m₁ m₂ (Sum.inr a)))
  map_add' v w := by ext a; simp
  map_smul' c v := by ext a; simp

/-- Inclusion of the first block. -/
def in₁L : Vec m₁ →ₗ[ℝ] Vec (m₁ + m₂) where
  toFun a := WithLp.toLp 2 (fun i => Sum.elim (⇑a) 0 ((dE m₁ m₂).symm i))
  map_add' v w := by
    ext i; simp only [PiLp.add_apply, PiLp.toLp_apply]
    generalize (dE m₁ m₂).symm i = j; rcases j with k | k <;> simp
  map_smul' c v := by
    ext i; simp only [PiLp.smul_apply, PiLp.toLp_apply]
    generalize (dE m₁ m₂).symm i = j; rcases j with k | k <;> simp

/-- Inclusion of the second block. -/
def in₂L : Vec m₂ →ₗ[ℝ] Vec (m₁ + m₂) where
  toFun b := WithLp.toLp 2 (fun i => Sum.elim 0 (⇑b) ((dE m₁ m₂).symm i))
  map_add' v w := by
    ext i; simp only [PiLp.add_apply, PiLp.toLp_apply]
    generalize (dE m₁ m₂).symm i = j; rcases j with k | k <;> simp
  map_smul' c v := by
    ext i; simp only [PiLp.smul_apply, PiLp.toLp_apply]
    generalize (dE m₁ m₂).symm i = j; rcases j with k | k <;> simp

def pr₁ : Vec (m₁ + m₂) →L[ℝ] Vec m₁ := LinearMap.toContinuousLinearMap pr₁L
def pr₂ : Vec (m₁ + m₂) →L[ℝ] Vec m₂ := LinearMap.toContinuousLinearMap pr₂L
def in₁ : Vec m₁ →L[ℝ] Vec (m₁ + m₂) := LinearMap.toContinuousLinearMap in₁L
def in₂ : Vec m₂ →L[ℝ] Vec (m₁ + m₂) := LinearMap.toContinuousLinearMap in₂L

lemma pr₁_apply (v : Vec (m₁ + m₂)) (a) : pr₁ v a = v (dE m₁ m₂ (Sum.inl a)) := rfl
lemma pr₂_apply (v : Vec (m₁ + m₂)) (a) : pr₂ v a = v (dE m₁ m₂ (Sum.inr a)) := rfl

lemma in₁_inl (a : Vec m₁) (k) : in₁ (m₂ := m₂) a (dE m₁ m₂ (Sum.inl k)) = a k := by
  show Sum.elim _ _ ((dE m₁ m₂).symm (dE m₁ m₂ _)) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma in₁_inr (a : Vec m₁) (k) : in₁ (m₂ := m₂) a (dE m₁ m₂ (Sum.inr k)) = 0 := by
  show Sum.elim _ _ ((dE m₁ m₂).symm (dE m₁ m₂ _)) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma in₂_inl (b : Vec m₂) (k) : in₂ (m₁ := m₁) b (dE m₁ m₂ (Sum.inl k)) = 0 := by
  show Sum.elim _ _ ((dE m₁ m₂).symm (dE m₁ m₂ _)) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma in₂_inr (b : Vec m₂) (k) : in₂ (m₁ := m₁) b (dE m₁ m₂ (Sum.inr k)) = b k := by
  show Sum.elim _ _ ((dE m₁ m₂).symm (dE m₁ m₂ _)) = _
  rw [Equiv.symm_apply_apply]; rfl

lemma in_pr (v : Vec (m₁ + m₂)) : in₁ (pr₁ v) + in₂ (pr₂ v) = v := by
  ext i
  obtain ⟨k, rfl⟩ := (dE m₁ m₂).surjective i
  rw [PiLp.add_apply]
  rcases k with k | k
  · rw [in₁_inl, in₂_inl, add_zero, pr₁_apply]
  · rw [in₁_inr, in₂_inr, zero_add, pr₂_apply]

lemma pr₁_in (a : Vec m₁) (b : Vec m₂) : pr₁ (in₁ a + in₂ b) = a := by
  ext k
  rw [pr₁_apply, PiLp.add_apply, in₁_inl, in₂_inl, add_zero]

lemma pr₂_in (a : Vec m₁) (b : Vec m₂) : pr₂ (in₁ a + in₂ b) = b := by
  ext k
  rw [pr₂_apply, PiLp.add_apply, in₁_inr, in₂_inr, zero_add]

lemma pr₁_in₁ (a : Vec m₁) : pr₁ (in₁ (m₂ := m₂) a) = a := by
  simpa using pr₁_in a (0 : Vec m₂)

lemma pr₂_in₁ (a : Vec m₁) : pr₂ (in₁ (m₂ := m₂) a) = 0 := by
  simpa using pr₂_in a (0 : Vec m₂)

lemma pr₁_in₂ (b : Vec m₂) : pr₁ (in₂ (m₁ := m₁) b) = 0 := by
  simpa using pr₁_in (0 : Vec m₁) b

lemma pr₂_in₂ (b : Vec m₂) : pr₂ (in₂ (m₁ := m₁) b) = b := by
  simpa using pr₂_in (0 : Vec m₁) b

lemma ext_pr {v w : Vec (m₁ + m₂)} (h₁ : pr₁ v = pr₁ w) (h₂ : pr₂ v = pr₂ w) : v = w := by
  rw [← in_pr v, ← in_pr w, h₁, h₂]

lemma diamond_vec (A : Mat m₁) (B : Mat m₂) (v : Vec (m₁ + m₂)) (k) :
    Matrix.toEuclideanLin (ConleyZehnder.diamond A B) v (dE m₁ m₂ k) =
      ∑ l, Matrix.fromBlocks A 0 0 B k l * v (dE m₁ m₂ l) := by
  rw [Matrix.toEuclideanLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct,
    ← (dE m₁ m₂).sum_comp]
  simp only [diamond_apply_dE]

lemma pr₁_diamond (A : Mat m₁) (B : Mat m₂) (v : Vec (m₁ + m₂)) :
    pr₁ (Matrix.toEuclideanLin (ConleyZehnder.diamond A B) v) =
      Matrix.toEuclideanLin A (pr₁ v) := by
  ext a
  rw [pr₁_apply, diamond_vec, Fintype.sum_sum_type]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, pr₁_apply]

lemma pr₂_diamond (A : Mat m₁) (B : Mat m₂) (v : Vec (m₁ + m₂)) :
    pr₂ (Matrix.toEuclideanLin (ConleyZehnder.diamond A B) v) =
      Matrix.toEuclideanLin B (pr₂ v) := by
  ext a
  rw [pr₂_apply, diamond_vec, Fintype.sum_sum_type]
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, pr₂_apply]

lemma diamond_in₁ (A : Mat m₁) (B : Mat m₂) (a : Vec m₁) :
    Matrix.toEuclideanLin (ConleyZehnder.diamond A B) (in₁ a) =
      in₁ (Matrix.toEuclideanLin A a) := by
  apply ext_pr
  · rw [pr₁_diamond, pr₁_in₁, pr₁_in₁]
  · rw [pr₂_diamond, pr₂_in₁, pr₂_in₁, map_zero]

lemma diamond_in₂ (A : Mat m₁) (B : Mat m₂) (b : Vec m₂) :
    Matrix.toEuclideanLin (ConleyZehnder.diamond A B) (in₂ b) =
      in₂ (Matrix.toEuclideanLin B b) := by
  apply ext_pr
  · rw [pr₁_diamond, pr₁_in₂, pr₁_in₂, map_zero]
  · rw [pr₂_diamond, pr₂_in₂, pr₂_in₂]

/-! ### Transport along a pointwise linear map -/

variable {a b : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Componentwise lift of a pointwise linear map to triples. -/
def tri (p : ℝ≥0∞) [Fact (1 ≤ p)] (L : Vec a →L[ℝ] Vec b) : Triple a p →L[ℝ] Triple b p :=
  (L.compLpL p cylMeasure).prodMap ((L.compLpL p cylMeasure).prodMap (L.compLpL p cylMeasure))

lemma partialS_comp (L : Vec a →L[ℝ] Vec b) {u : ℝ × ℝ → Vec a} (hu : Differentiable ℝ u)
    (x : ℝ × ℝ) : partialS (fun y => L (u y)) x = L (partialS u x) := by
  have h := (L.hasFDerivAt.comp x (hu x).hasFDerivAt).fderiv
  simp only [partialS]
  rw [show (fun y => L (u y)) = ⇑L ∘ u from rfl, h]
  rfl

lemma partialT_comp (L : Vec a →L[ℝ] Vec b) {u : ℝ × ℝ → Vec a} (hu : Differentiable ℝ u)
    (x : ℝ × ℝ) : partialT (fun y => L (u y)) x = L (partialT u x) := by
  have h := (L.hasFDerivAt.comp x (hu x).hasFDerivAt).fderiv
  simp only [partialT]
  rw [show (fun y => L (u y)) = ⇑L ∘ u from rfl, h]
  rfl

lemma isTestSection_comp (L : Vec a →L[ℝ] Vec b) {u : ℝ × ℝ → Vec a} (hu : IsTestSection u) :
    IsTestSection (fun y => L (u y)) := by
  obtain ⟨h1, h2, R, hR⟩ := hu
  exact ⟨L.contDiff.comp h1, fun s t => by simp only [h2 s t], R, fun s t h => by
    simp only [hR s t h, map_zero]⟩

lemma tri_mem_testTriples (L : Vec a →L[ℝ] Vec b) {w : Triple a p} (hw : w ∈ testTriples a p) :
    tri p L w ∈ testTriples b p := by
  obtain ⟨u, hu, h1, h2, h3⟩ := hw
  have hd : Differentiable ℝ u := hu.1.differentiable (by simp)
  refine ⟨fun y => L (u y), isTestSection_comp L hu, ?_, ?_, ?_⟩
  · filter_upwards [L.coeFn_compLpL (p := p) (μ := cylMeasure) w.1, h1] with x hx h
    change (L.compLpL p cylMeasure w.1) x = _
    rw [hx, h]
  · filter_upwards [L.coeFn_compLpL (p := p) (μ := cylMeasure) w.2.1, h2] with x hx h
    change (L.compLpL p cylMeasure w.2.1) x = _
    rw [hx, h, partialS_comp L hd]
  · filter_upwards [L.coeFn_compLpL (p := p) (μ := cylMeasure) w.2.2, h3] with x hx h
    change (L.compLpL p cylMeasure w.2.2) x = _
    rw [hx, h, partialT_comp L hd]

lemma tri_mem_W1p (L : Vec a →L[ℝ] Vec b) {w : Triple a p} (hw : w ∈ W1p p a) :
    tri p L w ∈ W1p p b := by
  have hle : W1p p a ≤ (W1p p b).comap (tri p L).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      intro w hw
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span (tri_mem_testTriples L hw))
    · exact (Submodule.isClosed_topologicalClosure _).preimage (tri p L).continuous
  exact hle hw

/-- `crApply` commutes with an intertwining pointwise map. -/
lemma crApply_tri (L : Vec a →L[ℝ] Vec b) (S : ℝ × ℝ → Mat a) (S' : ℝ × ℝ → Mat b)
    (hS : ∀ x v, L (Matrix.toEuclideanLin (S x) v) = Matrix.toEuclideanLin (S' x) (L v))
    (hJ : ∀ v, L (Matrix.toEuclideanLin (J₀ a) v) = Matrix.toEuclideanLin (J₀ b) (L v))
    (w : Triple a p) :
    crApply S' (tri p L w) =ᵐ[cylMeasure] fun x => L (crApply S w x) := by
  filter_upwards [L.coeFn_compLpL (p := p) (μ := cylMeasure) w.1,
    L.coeFn_compLpL (p := p) (μ := cylMeasure) w.2.1,
    L.coeFn_compLpL (p := p) (μ := cylMeasure) w.2.2] with x h1 h2 h3
  change (L.compLpL p cylMeasure w.2.1) x +
      Matrix.toEuclideanLin (J₀ b) ((L.compLpL p cylMeasure w.2.2) x) +
      Matrix.toEuclideanLin (S' x) ((L.compLpL p cylMeasure w.1) x) = _
  rw [h1, h2, h3, crApply, map_add, map_add, hS, hJ]

lemma tri_mem_crKernel (L : Vec a →L[ℝ] Vec b) (S : ℝ × ℝ → Mat a) (S' : ℝ × ℝ → Mat b)
    (hS : ∀ x v, L (Matrix.toEuclideanLin (S x) v) = Matrix.toEuclideanLin (S' x) (L v))
    (hJ : ∀ v, L (Matrix.toEuclideanLin (J₀ a) v) = Matrix.toEuclideanLin (J₀ b) (L v))
    {w : Triple a p} (hw : w ∈ crKernel p S) : tri p L w ∈ crKernel p S' := by
  have hle : crKernel p S ≤ (crKernel p S').comap (tri p L).toLinearMap := by
    rw [crKernel, Submodule.span_le]
    rintro w ⟨hw, h0⟩
    show tri p L w ∈ crKernel p S'
    refine Submodule.subset_span ⟨tri_mem_W1p L hw, ?_⟩
    filter_upwards [crApply_tri L S S' hS hJ w, h0] with x hx h
    rw [hx, h]
    simp
  exact hle hw

lemma compLpL_mem_crRange (L : Vec a →L[ℝ] Vec b) (S : ℝ × ℝ → Mat a) (S' : ℝ × ℝ → Mat b)
    (hS : ∀ x v, L (Matrix.toEuclideanLin (S x) v) = Matrix.toEuclideanLin (S' x) (L v))
    (hJ : ∀ v, L (Matrix.toEuclideanLin (J₀ a) v) = Matrix.toEuclideanLin (J₀ b) (L v))
    {f : LpCyl a p} (hf : f ∈ crRange p S) : L.compLpL p cylMeasure f ∈ crRange p S' := by
  have hle : crRange p S ≤ (crRange p S').comap (L.compLpL p cylMeasure).toLinearMap := by
    rw [crRange, Submodule.span_le]
    rintro f ⟨w, hw, hf⟩
    show L.compLpL p cylMeasure f ∈ crRange p S'
    refine Submodule.subset_span ⟨tri p L w, tri_mem_W1p L hw, ?_⟩
    filter_upwards [L.coeFn_compLpL (p := p) (μ := cylMeasure) f, hf,
      crApply_tri L S S' hS hJ w] with x h1 h2 h3
    rw [h1, h2, h3]
  exact hle hf

/-! ### The splittings of `L^p` and of triples -/

variable (p)

/-- `L^p(ℝ²⁽ᵐ¹⁺ᵐ²⁾) ≃ L^p(ℝ²ᵐ¹) × L^p(ℝ²ᵐ²)`. -/
def splitLp : LpCyl (m₁ + m₂) p ≃ₗ[ℝ] LpCyl m₁ p × LpCyl m₂ p where
  toFun f := (pr₁.compLpL p cylMeasure f, pr₂.compLpL p cylMeasure f)
  invFun y := in₁.compLpL p cylMeasure y.1 + in₂.compLpL p cylMeasure y.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (in₁.compLpL p cylMeasure (pr₁.compLpL p cylMeasure f))
        (in₂.compLpL p cylMeasure (pr₂.compLpL p cylMeasure f)),
      in₁.coeFn_compLpL (p := p) (μ := cylMeasure) (pr₁.compLpL p cylMeasure f),
      in₂.coeFn_compLpL (p := p) (μ := cylMeasure) (pr₂.compLpL p cylMeasure f),
      pr₁.coeFn_compLpL (p := p) (μ := cylMeasure) f,
      pr₂.coeFn_compLpL (p := p) (μ := cylMeasure) f] with x h h1 h2 h3 h4
    rw [h, Pi.add_apply, h1, h2, h3, h4, in_pr]
  right_inv y := by
    obtain ⟨y₁, y₂⟩ := y
    ext1
    · apply Lp.ext
      filter_upwards [pr₁.coeFn_compLpL (p := p) (μ := cylMeasure)
          (in₁.compLpL p cylMeasure y₁ + in₂.compLpL p cylMeasure y₂),
        Lp.coeFn_add (in₁.compLpL p cylMeasure y₁) (in₂.compLpL p cylMeasure y₂),
        in₁.coeFn_compLpL (p := p) (μ := cylMeasure) y₁,
        in₂.coeFn_compLpL (p := p) (μ := cylMeasure) y₂] with x h h0 h1 h2
      change (pr₁.compLpL p cylMeasure
        (in₁.compLpL p cylMeasure y₁ + in₂.compLpL p cylMeasure y₂)) x = _
      rw [h, h0, Pi.add_apply, h1, h2, pr₁_in]
    · apply Lp.ext
      filter_upwards [pr₂.coeFn_compLpL (p := p) (μ := cylMeasure)
          (in₁.compLpL p cylMeasure y₁ + in₂.compLpL p cylMeasure y₂),
        Lp.coeFn_add (in₁.compLpL p cylMeasure y₁) (in₂.compLpL p cylMeasure y₂),
        in₁.coeFn_compLpL (p := p) (μ := cylMeasure) y₁,
        in₂.coeFn_compLpL (p := p) (μ := cylMeasure) y₂] with x h h0 h1 h2
      change (pr₂.compLpL p cylMeasure
        (in₁.compLpL p cylMeasure y₁ + in₂.compLpL p cylMeasure y₂)) x = _
      rw [h, h0, Pi.add_apply, h1, h2, pr₂_in]

/-- Triples split componentwise. -/
def splitTriple : Triple (m₁ + m₂) p ≃ₗ[ℝ] Triple m₁ p × Triple m₂ p where
  toFun w := (((splitLp p w.1).1, (splitLp p w.2.1).1, (splitLp p w.2.2).1),
    ((splitLp p w.1).2, (splitLp p w.2.1).2, (splitLp p w.2.2).2))
  invFun y := ((splitLp p).symm (y.1.1, y.2.1), (splitLp p).symm (y.1.2.1, y.2.2.1),
    (splitLp p).symm (y.1.2.2, y.2.2.2))
  map_add' w w' := by simp
  map_smul' c w := by simp
  left_inv w := by simp
  right_inv y := by simp

variable {p}

lemma splitTriple_apply (w : Triple (m₁ + m₂) p) :
    splitTriple p w = (tri p pr₁ w, tri p pr₂ w) := rfl

lemma splitTriple_symm_apply (y : Triple m₁ p × Triple m₂ p) :
    (splitTriple p).symm y = tri p in₁ y.1 + tri p in₂ y.2 := rfl

lemma splitLp_apply (f : LpCyl (m₁ + m₂) p) :
    splitLp p f = (pr₁.compLpL p cylMeasure f, pr₂.compLpL p cylMeasure f) := rfl

lemma splitLp_symm_apply (y : LpCyl m₁ p × LpCyl m₂ p) :
    (splitLp p).symm y = in₁.compLpL p cylMeasure y.1 + in₂.compLpL p cylMeasure y.2 := rfl

/-! ### Kernel and range split -/

section

variable (S₁ : ℝ × ℝ → Mat m₁) (S₂ : ℝ × ℝ → Mat m₂)

lemma hJ_pr₁ (v : Vec (m₁ + m₂)) :
    pr₁ (Matrix.toEuclideanLin (J₀ (m₁ + m₂)) v) = Matrix.toEuclideanLin (J₀ m₁) (pr₁ v) := by
  rw [J_eq_diamond, pr₁_diamond]

lemma hJ_pr₂ (v : Vec (m₁ + m₂)) :
    pr₂ (Matrix.toEuclideanLin (J₀ (m₁ + m₂)) v) = Matrix.toEuclideanLin (J₀ m₂) (pr₂ v) := by
  rw [J_eq_diamond, pr₂_diamond]

lemma hJ_in₁ (v : Vec m₁) :
    in₁ (Matrix.toEuclideanLin (J₀ m₁) v) =
      Matrix.toEuclideanLin (J₀ (m₁ + m₂)) (in₁ v) := by
  rw [J_eq_diamond, diamond_in₁]

lemma hJ_in₂ (v : Vec m₂) :
    in₂ (Matrix.toEuclideanLin (J₀ m₂) v) =
      Matrix.toEuclideanLin (J₀ (m₁ + m₂)) (in₂ v) := by
  rw [J_eq_diamond, diamond_in₂]

lemma crKernel_eq :
    crKernel p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x)) =
      ((crKernel p S₁).prod (crKernel p S₂)).comap (splitTriple p).toLinearMap := by
  apply le_antisymm
  · intro w hw
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, splitTriple_apply]
    exact ⟨tri_mem_crKernel pr₁ _ S₁ (fun x v => pr₁_diamond _ _ v) hJ_pr₁ hw,
      tri_mem_crKernel pr₂ _ S₂ (fun x v => pr₂_diamond _ _ v) hJ_pr₂ hw⟩
  · intro w hw
    rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw
    rw [← (splitTriple p).symm_apply_apply w, splitTriple_symm_apply]
    exact Submodule.add_mem _
      (tri_mem_crKernel in₁ S₁ _ (fun x v => (diamond_in₁ _ _ v).symm) hJ_in₁ hw.1)
      (tri_mem_crKernel in₂ S₂ _ (fun x v => (diamond_in₂ _ _ v).symm) hJ_in₂ hw.2)

lemma crRange_eq :
    crRange p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x)) =
      ((crRange p S₁).prod (crRange p S₂)).comap (splitLp p).toLinearMap := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, splitLp_apply]
    exact ⟨compLpL_mem_crRange pr₁ _ S₁ (fun x v => pr₁_diamond _ _ v) hJ_pr₁ hf,
      compLpL_mem_crRange pr₂ _ S₂ (fun x v => pr₂_diamond _ _ v) hJ_pr₂ hf⟩
  · intro f hf
    rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hf
    rw [← (splitLp p).symm_apply_apply f, splitLp_symm_apply]
    exact Submodule.add_mem _
      (compLpL_mem_crRange in₁ S₁ _ (fun x v => (diamond_in₁ _ _ v).symm) hJ_in₁ hf.1)
      (compLpL_mem_crRange in₂ S₂ _ (fun x v => (diamond_in₂ _ _ v).symm) hJ_in₂ hf.2)

end

/-! ### Linear algebra -/

/-- `A.prod B ≃ A × B`. -/
def prodSubEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (A : Submodule R M) (B : Submodule R N) : (A.prod B) ≃ₗ[R] A × B where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

lemma finrank_comap_equiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) (X : Submodule R N) :
    Module.finrank R (X.comap e.toLinearMap) = Module.finrank R X := by
  have h := (e.symm.submoduleMap X).finrank_eq
  rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm] at h
  exact h.symm

/-- `M ⧸ comap e (A.prod B) ≃ (M₁ ⧸ A) × (M₂ ⧸ B)`. -/
def quotCompEquiv {R M M₁ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] (e : M ≃ₗ[R] M₁ × M₂) (A : Submodule R M₁)
    (B : Submodule R M₂) : (M ⧸ (A.prod B).comap e.toLinearMap) ≃ₗ[R] (M₁ ⧸ A) × (M₂ ⧸ B) :=
  let Q : M →ₗ[R] (M₁ ⧸ A) × (M₂ ⧸ B) := (A.mkQ.prodMap B.mkQ).comp e.toLinearMap
  have hker : LinearMap.ker Q = (A.prod B).comap e.toLinearMap := by
    simp only [Q, LinearMap.ker_comp, LinearMap.ker_prodMap, Submodule.ker_mkQ]
  have hsurj : Function.Surjective Q :=
    (Function.Surjective.prodMap A.mkQ_surjective B.mkQ_surjective).comp e.surjective
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (Q.quotKerEquivOfSurjective hsurj)

/-! ### The index -/

theorem crIndex_diamond_aux {m₁ m₂ : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (S₁ : ℝ × ℝ → Mat m₁)
    (S₂ : ℝ × ℝ → Mat m₂) (h₁ : IsFredholmCR p S₁) (h₂ : IsFredholmCR p S₂) :
    crIndex p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x)) = crIndex p S₁ + crIndex p S₂ := by
  haveI := h₁.1
  haveI := h₂.1
  haveI := h₁.2.2
  haveI := h₂.2.2
  have hK : Module.finrank ℝ (crKernel p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x))) =
      Module.finrank ℝ (crKernel p S₁) + Module.finrank ℝ (crKernel p S₂) := by
    rw [crKernel_eq, finrank_comap_equiv, (prodSubEquiv _ _).finrank_eq, Module.finrank_prod]
  have hC : Module.finrank ℝ (LpCyl (m₁ + m₂) p ⧸
        crRange p (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x))) =
      Module.finrank ℝ (LpCyl m₁ p ⧸ crRange p S₁) +
        Module.finrank ℝ (LpCyl m₂ p ⧸ crRange p S₂) := by
    rw [crRange_eq, (quotCompEquiv _ _ _).finrank_eq, Module.finrank_prod]
  unfold crIndex
  rw [hK, hC]
  push_cast
  ring

end CRIFC2

open CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

theorem solution {a b : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (L : Vec a →L[ℝ] Vec b)
    {w : Triple a p} (hw : w ∈ W1p p a) :
    (L.compLpL p cylMeasure w.1, L.compLpL p cylMeasure w.2.1, L.compLpL p cylMeasure w.2.2) ∈
      W1p p b :=
  CRIFC2.tri_mem_W1p L hw
