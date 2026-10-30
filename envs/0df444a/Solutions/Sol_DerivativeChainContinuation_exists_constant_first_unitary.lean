-- Prove2me | solution 1 for DerivativeChainContinuation.exists_constant_first_unitary
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:48:18.865657+00:00
-- url     : https://prove2.me/submissions/f2e1a2b6-e665-4463-bba6-a22940325f7e

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


theorem solution (n : ℕ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      ∀ i, Q i 0 = ((Real.sqrt (n+1 : ℝ))⁻¹ : ℂ) := by
  let c : ℂ := ((Real.sqrt (n+1 : ℝ))⁻¹ : ℂ)
  let w : EuclideanSpace ℂ (Fin (n+1)) := WithLp.toLp 2 (fun _ => c)
  have hn : (0 : ℝ) < n+1 := by positivity
  have hc : ‖c‖^2=(n+1:ℝ)⁻¹ := by
    simp only [c, norm_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow]
    rw [Real.sq_sqrt hn.le]
  have hwn : ‖w‖=1 := by
    have hh : ‖w‖^2=1 := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ _ : Fin (n+1), ‖c‖^2)=1
      simp only [hc, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact mul_inv_cancel₀ (ne_of_gt hn)
    nlinarith [norm_nonneg w]
  have hon : Orthonormal ℂ (({0} : Set (Fin (n+1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hwn
  obtain ⟨b,hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n+1)))=Fintype.card (Fin (n+1)))
  let e := EuclideanSpace.basisFun (Fin (n+1)) ℂ
  refine ⟨e.toBasis.toMatrix b.toBasis,e.toMatrix_orthonormalBasis_mem_unitary b,?_⟩
  intro i
  simp [Module.Basis.toMatrix_apply, hb 0 (by simp), e, w, c]
