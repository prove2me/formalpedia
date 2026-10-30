-- Prove2me | solution 1 for DerivativeChainContinuation.regularizedGram_unitary
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:12:57.844+00:00
-- url     : https://prove2.me/submissions/dd6c1000-aded-482b-881c-c8bb326aa510

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (t : ℝ) :
    regularizedGram (Q.conjTranspose*M*Q) t=Q.conjTranspose*regularizedGram M t*Q := by
  have hQQ : Q*Q.conjTranspose=1 := mem_unitaryGroup_iff.mp hQ
  have hQsQ : Q.conjTranspose*Q=1 := mem_unitaryGroup_iff'.mp hQ
  have he : (Q.conjTranspose*M*Q).conjTranspose*(Q.conjTranspose*M*Q) =
      Q.conjTranspose*(M.conjTranspose*M)*Q := by
    calc
      _ = Q.conjTranspose*(M.conjTranspose*(Q*Q.conjTranspose)*M)*Q := by
        simp only [conjTranspose_mul,conjTranspose_conjTranspose,Matrix.mul_assoc]
      _ = _ := by rw [hQQ,mul_one]
  have hc : Q.conjTranspose*diagonal (fun _ => (t:ℂ))*Q=diagonal (fun _ => (t:ℂ)) := by
    rw [← smul_one_eq_diagonal]
    simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,hQsQ]
  simp only [regularizedGram,he,mul_add,add_mul,hc]
