-- Prove2me | solution 1 for BaconThesis.DFS.eq_5_14
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:01:18.397111+00:00
-- url     : https://prove2.me/submissions/dca32354-42e6-4c05-81d6-7e6c122b2c28

import Mathlib
import Definitions.Def_BaconThesis_DFS_osrOp

open scoped Matrix Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace BaconThesis.DFS.SolM5_14

open BaconThesis.DFS

section calculus

variable {T : Type} [Fintype T] [DecidableEq T]

open scoped Matrix.Norms.Operator in
/-- If `X` and `Y` agree on the range of `Q` and `Y` commutes with `Q`, so do their exponentials. -/
lemma exp_mul_eq (X Y Q : Matrix T T ℂ) (hXY : X * Q = Y * Q) (hYQ : Y * Q = Q * Y)
    (z : ℂ) : NormedSpace.exp (z • X) * Q = NormedSpace.exp (z • Y) * Q := by
  have hpow : ∀ k : ℕ, X ^ k * Q = Y ^ k * Q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hXY, hYQ, ← mul_assoc, ih, mul_assoc, ← hYQ, ← mul_assoc,
        ← pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • X)).mul_right Q
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • Y)).mul_right Q
  have heq : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • (z • X) ^ k) * Q =
      ((k.factorial : ℂ)⁻¹ • (z • Y) ^ k) * Q := by
    intro k
    rw [smul_pow, smul_pow, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, hpow]
  simp only [heq] at h1
  exact h1.unique h2

end calculus

variable {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

lemma exp_one_kronecker (Y : Matrix e e ℂ) :
    NormedSpace.exp ((1 : Matrix s s ℂ) ⊗ₖ Y) = (1 : Matrix s s ℂ) ⊗ₖ NormedSpace.exp Y := by
  let f : Matrix e e ℂ →+* Matrix (s × e) (s × e) ℂ :=
    { toFun := fun Y => (1 : Matrix s s ℂ) ⊗ₖ Y
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun A B => by rw [← Matrix.mul_kronecker_mul, one_mul]
      map_zero' := Matrix.kronecker_zero _
      map_add' := fun A B => Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_matrix fun i j => ?_
    change Continuous fun Y : Matrix e e ℂ => (1 : Matrix s s ℂ) i.1 j.1 * Y i.2 j.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

/-- The product vector `j ⊗ w`. -/
def tens (j : s → ℂ) (w : e → ℂ) : s × e → ℂ := fun p => j p.1 * w p.2

lemma proj_mulVec (j : s → ℂ) (w : e → ℂ) :
    (Matrix.vecMulVec j (star j) ⊗ₖ (1 : Matrix e e ℂ)) *ᵥ tens j w = (star j ⬝ᵥ j) • tens j w := by
  ext ⟨a, k⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tens, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma one_kron_mulVec (V : Matrix e e ℂ) (j : s → ℂ) (w : e → ℂ) :
    ((1 : Matrix s s ℂ) ⊗ₖ V) *ᵥ tens j w = tens j (V *ᵥ w) := by
  ext ⟨a, k⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tens, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.mul_sum]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring


lemma osrOp_mulVec (H : Matrix (s × e) (s × e) ℂ) (t : ℝ) (φ ψ : e → ℂ) (j : s → ℂ) (a : s) :
    (osrOp H t φ ψ *ᵥ j) a = ∑ k, star (φ k) * (evolOp H t *ᵥ tens j ψ) (a, k) := by
  simp only [osrOp, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, tens,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end BaconThesis.DFS.SolM5_14

open BaconThesis.DFS BaconThesis.DFS.SolM5_14 in
theorem solution {s e ι : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    [Fintype ι]
    (Sα : ι → Matrix s s ℂ) (Bα : ι → Matrix e e ℂ) (W : Submodule ℂ (s → ℂ))
    (c : ι → ℂ) (hc : ∀ α, ∀ j ∈ W, Sα α *ᵥ j = c α • j) (t : ℝ) (φ ψ : e → ℂ) :
    ∀ j ∈ W, osrOp (∑ α, Sα α ⊗ₖ Bα α) t φ ψ *ᵥ j =
      (star φ ⬝ᵥ (evolOp (∑ α, c α • Bα α) t *ᵥ ψ)) • j := by
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0
    simp
  set H := ∑ α, Sα α ⊗ₖ Bα α with hHdef
  set P := Matrix.vecMulVec j (star j) with hP
  set Bc : Matrix e e ℂ := ∑ α, c α • Bα α with hBc
  set Q : Matrix (s × e) (s × e) ℂ := P ⊗ₖ (1 : Matrix e e ℂ) with hQ
  set K : Matrix (s × e) (s × e) ℂ := (1 : Matrix s s ℂ) ⊗ₖ Bc with hK
  have hKQ : K * Q = P ⊗ₖ Bc := by
    rw [hK, hQ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hQK : Q * K = P ⊗ₖ Bc := by
    rw [hK, hQ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hHQ : H * Q = K * Q := by
    rw [hKQ, hHdef, hQ, Finset.sum_mul, hBc]
    simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    have : ∀ α, Sα α * P = c α • P := by
      intro α
      rw [hP, Matrix.mul_vecMulVec, hc α j hj, Matrix.smul_vecMulVec]
    simp only [this]
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp [Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  set z : ℂ := -(t : ℂ) * Complex.I with hz
  have hexp := exp_mul_eq H K Q hHQ (hKQ.trans hQK.symm) z
  set V : Matrix e e ℂ := NormedSpace.exp (z • Bc) with hV
  have hUQ : evolOp H t * Q = ((1 : Matrix s s ℂ) ⊗ₖ V) * Q := by
    rw [evolOp, hexp, hK, ← Matrix.kronecker_smul, exp_one_kronecker]
  have hjj : star j ⬝ᵥ j ≠ 0 := mt dotProduct_star_self_eq_zero.mp hj0
  have hUx : evolOp H t *ᵥ tens j ψ = tens j (V *ᵥ ψ) := by
    have h1 := congrArg (· *ᵥ tens j ψ) hUQ
    rw [hQ, hP] at h1
    simp only [← Matrix.mulVec_mulVec, proj_mulVec, Matrix.mulVec_smul, one_kron_mulVec] at h1
    exact smul_right_injective _ hjj h1
  have hVdef : evolOp Bc t = V := rfl
  ext a
  rw [osrOp_mulVec, hUx, hVdef]
  simp only [tens, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
