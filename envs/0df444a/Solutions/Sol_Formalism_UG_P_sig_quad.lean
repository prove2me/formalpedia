-- Prove2me | solution 1 for Formalism.UG.P.sig_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:06.053686+00:00
-- url     : https://prove2.me/submissions/616c27c6-22b2-49a2-b8f7-6ac3b12d1ec3

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]
  simp [Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
    Matrix.neg_mulVec, Finset.sum_neg_distrib]
end Formalism.UG.P
