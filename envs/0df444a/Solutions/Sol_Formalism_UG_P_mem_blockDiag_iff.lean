-- Prove2me | solution 1 for Formalism.UG.P.mem_blockDiag_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:01.036798+00:00
-- url     : https://prove2.me/submissions/1572fc92-4ca6-4170-90eb-94fed22d6e07

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.blockDiag p q ↔
      Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q := by
  simp only [Formalism.UG.blockDiag, Set.mem_setOf_eq]
  rw [Jpq_eq_diagonal]
  constructor
  · intro h
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rcases a with i | i <;> rcases b with j | j
    · simp
    · simp [(h i j).1]
    · simp [(h j i).2]
    · simp
  · intro h i j
    have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    have h2 := congrFun (congrFun h (Sum.inr j)) (Sum.inl i)
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1 h2
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, mul_one, mul_neg, neg_mul] at h1 h2
    constructor
    · first | exact h1 | linear_combination h1 / 2 | linear_combination -h1 / 2
    · first | exact h2 | linear_combination h2 / 2 | linear_combination -h2 / 2
end Formalism.UG.P
