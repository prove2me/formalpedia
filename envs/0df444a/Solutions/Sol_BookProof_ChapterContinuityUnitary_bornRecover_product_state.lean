-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.bornRecover_product_state
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:41:25.682989+00:00
-- url     : https://prove2.me/submissions/a1e68469-5baf-43cf-8d52-07509fe92c0a

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary
variable {N : ℕ} [NeZero N]
open scoped BigOperators Matrix TensorProduct
variable {X : Type*}

theorem solution (f : X → ℂ) (e0 : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ = 1) (he0 : ∑ z, ‖e0 z‖ ^ 2 = 1)
    (v : X → (ZMod N → ℝ)) (t : ℝ) (x : X) :
    bornRecover (v x) t (fun z => productState X f e0 (x, z)) Finset.univ = 1 := by
  simp only [bornRecover, evolvedState, productState]
  rw [unitary_preserves_normSq _ (continuityUnitary_unitary (v x) t)]
  simp only [tensorIsom, LinearEquiv.trans_apply, swapCurry, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  simp [norm_mul, mul_pow, hf, mul_one, Finset.mul_sum, he0]
