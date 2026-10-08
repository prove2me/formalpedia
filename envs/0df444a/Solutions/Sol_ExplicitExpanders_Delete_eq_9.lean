-- Prove2me | solution 1 for ExplicitExpanders.Delete.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:00:09.858227+00:00
-- url     : https://prove2.me/submissions/7ae6d476-66f6-4158-9ad7-098e0e66590b

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

set_option autoImplicit false
set_option linter.deprecated false

open Matrix WithLp in
theorem eq9_core {V : Type*} [Fintype V] (A : Matrix V V ℝ) (n d : ℕ) (lam : ℝ)
    (hA : ExplicitExpanders.Delete.IsNDLambdaMatrix A n d lam) (g : V → ℝ)
    (hg : ∑ x, g x = 0) :
    |g ⬝ᵥ (A *ᵥ g)| ≤ lam * ∑ x, g x ^ 2 := by
  classical
  obtain ⟨hsym, -, hone, heig⟩ := hA
  set T := Matrix.toEuclideanLin A with hT_def
  have hH : A.IsHermitian := by
    unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hsym
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  let W : Submodule ℝ (EuclideanSpace ℝ V) :=
    { carrier := {x | ∑ i, ofLp x i = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, ofLp_add, Pi.add_apply, Finset.sum_add_distrib] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, ofLp_smul, Pi.smul_apply, smul_eq_mul,
          ← Finset.mul_sum] at *
        rw [hx, mul_zero] }
  have hmemW : ∀ x : EuclideanSpace ℝ V, x ∈ W ↔ ∑ i, ofLp x i = 0 := fun x => Iff.rfl
  have hcol : ∀ j, ∑ i, A i j = d := by
    intro j
    have h1 := congrFun hone j
    simp only [mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => hsym.apply j i
  have hTW : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    rw [hmemW] at hx ⊢
    change ∑ i, (A *ᵥ ofLp x) i = 0
    simp only [mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hcol, ← Finset.mul_sum, hx, mul_zero]
  set S := T.restrict hTW with hS_def
  have hS : S.IsSymmetric := hT.restrict_invariant hTW
  set b := hS.eigenvectorBasis (rfl : Module.finrank ℝ W = Module.finrank ℝ W) with hb
  set μ := hS.eigenvalues (rfl : Module.finrank ℝ W = Module.finrank ℝ W) with hμdef
  have hμ : ∀ i, |μ i| ≤ lam := by
    intro i
    have h1 : S (b i) = (μ i : ℝ) • b i := hS.apply_eigenvectorBasis rfl i
    have hne : b i ≠ 0 := b.orthonormal.ne_zero i
    apply heig (μ i) (ofLp ((b i : W) : EuclideanSpace ℝ V))
    · intro h
      apply hne
      apply Subtype.ext
      apply (WithLp.ofLp_injective 2)
      rw [h]; rfl
    · exact (b i).2
    · have h2 := congrArg (fun y : W => ofLp (y : EuclideanSpace ℝ V)) h1
      exact h2
  set x : W := ⟨toLp 2 g, by rw [hmemW]; exact hg⟩ with hx
  have hexp : inner ℝ (S x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
    rw [← b.sum_inner_mul_inner (S x) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS x (b i), hS.apply_eigenvectorBasis rfl i, inner_smul_right, real_inner_comm x (b i)]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have hnorm : ∑ i, (inner ℝ (b i) x) ^ 2 = inner ℝ x x := by
    rw [← b.sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]; ring
  have hQ : g ⬝ᵥ (A *ᵥ g) = inner ℝ (S x) x := by
    rw [Submodule.coe_inner]
    change g ⬝ᵥ (A *ᵥ g) = inner ℝ (toLp 2 (A *ᵥ g)) (toLp 2 g)
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct]
  have hN : ∑ v, g v ^ 2 = inner ℝ x x := by
    rw [Submodule.coe_inner]
    change ∑ v, g v ^ 2 = inner ℝ (toLp 2 g) (toLp 2 g)
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, sq]
  rw [hQ, hN, hexp, ← hnorm, Finset.mul_sum]
  calc |∑ i, μ i * (inner ℝ (b i) x) ^ 2| ≤ ∑ i, |μ i * (inner ℝ (b i) x) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, lam * (inner ℝ (b i) x) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg (inner ℝ (b i) x))]
        exact mul_le_mul_of_nonneg_right (hμ i) (sq_nonneg _)

namespace ExplicitExpanders.Delete

open Matrix in
theorem eq9_ext {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) [DecidableRel (deleted H U).Adj] (f : Kept U → ℝ) :
    ∃ g : V → ℝ, ∑ v, g v = ∑ x, f x ∧ ∑ v, g v ^ 2 = ∑ x, f x ^ 2 ∧
      g ⬝ᵥ (H.adjMatrix ℝ *ᵥ g) = f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f) := by
  let g : V → ℝ := fun v => if h : v ∈ U then 0 else f ⟨v, h⟩
  have hF : ∀ F : V → ℝ, ∑ v, g v * F v = ∑ x : Kept U, f x * F x.1 := by
    intro F
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ U)]
    rw [Finset.sum_eq_zero (fun i _ => by simp [g, i.2]), zero_add]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun i => by simp [g, i.2])
  refine ⟨g, ?_, ?_, ?_⟩
  · have := hF (fun _ => 1); simpa using this
  · have := hF g
    rw [show (∑ v, g v ^ 2) = ∑ v, g v * g v from by simp [sq]]
    rw [this, show (∑ x : Kept U, f x ^ 2) = ∑ x : Kept U, f x * f x from by simp [sq]]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [g, i.2]
  · simp only [dotProduct, mulVec]
    rw [hF]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have := hF (fun w => H.adjMatrix ℝ x.1 w)
    rw [show (∑ w, H.adjMatrix ℝ x.1 w * g w) = ∑ w, g w * H.adjMatrix ℝ x.1 w from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, this]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm]
    congr 1
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    split_ifs with h1 h2 h2 <;> simp_all [deleted]

end ExplicitExpanders.Delete

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
theorem eq_9' {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (n d : ℕ) (lam : ℝ)
    (hH : IsNDLambda H n d lam) (U : Finset V) (f : Kept U → ℝ) (hf : ∑ x, f x = 0) :
    |f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f)| ≤ lam * ∑ x, f x ^ 2 := by
  obtain ⟨g, hg1, hg2, hg3⟩ := eq9_ext H U f
  rw [← hg3, ← hg2]
  exact eq9_core _ n d lam hH.2 g (hg1.trans hf)

end ExplicitExpanders.Delete

open Classical Matrix ExplicitExpanders.Delete in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (n d : ℕ) (lam : ℝ)
    (hH : IsNDLambda H n d lam) (U : Finset V) (f : Kept U → ℝ) (hf : ∑ x, f x = 0) :
    |f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f)| ≤ lam * ∑ x, f x ^ 2 := by
  exact ExplicitExpanders.Delete.eq_9' H n d lam hH U f hf
