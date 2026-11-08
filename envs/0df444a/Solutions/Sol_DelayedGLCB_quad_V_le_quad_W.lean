-- Prove2me | solution 1 for DelayedGLCB.quad_V_le_quad_W
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:27:51.483288+00:00
-- url     : https://prove2.me/submissions/d23b8272-95b2-4396-9ddf-d43f6b644c4b

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_DUCB

open Matrix MostlyExplorationFree.GreedyBandit

namespace Aux_DGLCB

open DelayedGLCB

lemma quad_outer {d : ℕ} (x v : Fin d → ℝ) : v ⬝ᵥ (outer x *ᵥ v) = (v ⬝ᵥ x) ^ 2 := by
  have h : outer x *ᵥ v = (x ⬝ᵥ v) • x := by
    ext i
    simp only [outer, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, dotProduct_smul, smul_eq_mul, dotProduct_comm x v]
  ring

lemma quad_sum {d : ℕ} (S : Finset ℕ) (X : ℕ → Fin d → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ ((∑ s ∈ S, outer (X s)) *ᵥ v) = ∑ s ∈ S, (v ⬝ᵥ X s) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun s _ => quad_outer _ _

end Aux_DGLCB

open DelayedGLCB in
theorem solution {Ω : Type*} {d K : ℕ} (A : DUCB d K) (E : Env Ω d K) (ω : Ω)
    (hx : ∀ s a, l2norm (E.x s ω a) ≤ 1) (t : ℕ) (v : Fin d → ℝ) :
    (v ⬝ᵥ (V A E ω t *ᵥ v)
        = v ⬝ᵥ (W A E ω t *ᵥ v) + ∑ s ∈ missingSet E.D ω t, (v ⬝ᵥ X A E ω s) ^ 2) ∧
    v ⬝ᵥ (V A E ω t *ᵥ v)
      ≤ v ⬝ᵥ (W A E ω t *ᵥ v) + (missingCount E.D ω t : ℝ) * l2norm v ^ 2 := by
  have h1 : v ⬝ᵥ (V A E ω t *ᵥ v)
      = v ⬝ᵥ (W A E ω t *ᵥ v) + ∑ s ∈ missingSet E.D ω t, (v ⬝ᵥ X A E ω s) ^ 2 := by
    unfold V W Vmat Wmat
    rw [Aux_DGLCB.quad_sum, Aux_DGLCB.quad_sum]
    unfold completeSet missingSet
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  refine ⟨h1, ?_⟩
  rw [h1]
  have hvv : l2norm v ^ 2 = v ⬝ᵥ v := by
    unfold l2norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hb : ∀ s, (v ⬝ᵥ X A E ω s) ^ 2 ≤ v ⬝ᵥ v := by
    intro s
    have hxx : X A E ω s ⬝ᵥ X A E ω s ≤ 1 := by
      have := hx s (action A E ω s)
      unfold l2norm at this
      exact Real.sqrt_le_one.mp this
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (X A E ω s)
    have e1 : v ⬝ᵥ X A E ω s = ∑ i, v i * X A E ω s i := rfl
    have e2 : v ⬝ᵥ v = ∑ i, v i ^ 2 := by
      simp only [dotProduct, sq]
    have e3 : X A E ω s ⬝ᵥ X A E ω s = ∑ i, X A E ω s i ^ 2 := by
      simp only [dotProduct, sq]
    rw [e1, e2]
    rw [e3] at hxx
    have hv0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  have hsum : ∑ s ∈ missingSet E.D ω t, (v ⬝ᵥ X A E ω s) ^ 2 ≤
      (missingCount E.D ω t : ℝ) * (v ⬝ᵥ v) := by
    calc ∑ s ∈ missingSet E.D ω t, (v ⬝ᵥ X A E ω s) ^ 2
        ≤ ∑ s ∈ missingSet E.D ω t, v ⬝ᵥ v := Finset.sum_le_sum fun s _ => hb s
      _ = (missingCount E.D ω t : ℝ) * (v ⬝ᵥ v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
  rw [hvv]
  linarith
