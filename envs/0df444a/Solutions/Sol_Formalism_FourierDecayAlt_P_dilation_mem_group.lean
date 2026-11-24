-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_mem_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:22.691801+00:00
-- url     : https://prove2.me/submissions/06854c50-fa54-4232-a191-a542b9c36ae6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace B2
end B2
private lemma star_ofReal_eq_self (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.DilMem := by
  unfold Formalism.FourierDecayAlt.B.DilMem
  intro k r t ht
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  unfold GV UH aDil
  rw [Set.mem_setOf_eq, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Hpk
  beta_reduce
  split_ifs
  all_goals (try simp only [star_ofReal_eq_self, star_one, mul_one, one_mul, mul_zero, zero_mul, mul_neg])
  all_goals try first
    | rfl
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | (rw [show (j : ℕ) - (r + k) = r - (i : ℕ) by omega, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (hp _), Complex.ofReal_one])
    | (rw [show (i : ℕ) - (r + k) = r - (j : ℕ) by omega, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (hp _), Complex.ofReal_one])
end Formalism.FourierDecayAlt.P
