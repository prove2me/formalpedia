-- Prove2me | solution 1 for DerivativeChainContinuation.positive_scaled_rank_one_determinant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:20:19.929236+00:00
-- url     : https://prove2.me/submissions/657d72c3-cecb-441d-aa68-2273ccd3ea01

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_rank_one_determinant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder


open DerivativeChainContinuation in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (u : Fin n → ℂ) (s : ℝ) (hs : 0 ≤ s) :
    ‖A.det‖ ≤ ‖(A+(s:ℂ) • vecMulVec u (star u)).det‖ := by
  let v := fun i => (Real.sqrt s:ℂ)*u i
  have he : vecMulVec v (star v)=(s:ℂ) • vecMulVec u (star u) := by
    have hsq : (Real.sqrt s:ℂ)*(Real.sqrt s:ℂ)=(s:ℂ) := by
      rw [← pow_two,← Complex.ofReal_pow,Real.sq_sqrt hs]
    ext i j
    simp only [vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,Pi.star_apply,v,
      star_mul,Complex.star_def,map_mul,Complex.conj_ofReal]
    calc
      _ = ((Real.sqrt s:ℂ)*(Real.sqrt s:ℂ))*(u i*(starRingEnd ℂ) (u j)) := by ring
      _ = _ := by rw [hsq]
  simpa only [he] using positive_rank_one_determinant A hA v
