-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2.aDil_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:31:35.813803+00:00
-- url     : https://prove2.me/submissions/05eafccd-1fde-4ed3-81d3-153a31a504ed

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open Formalism.FourierDecayAlt.P.B2
namespace Formalism.FourierDecayAlt.P.B2
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, inv_pow, inv_mul_cancel₀ (hp _), Complex.ofReal_one]
  · exact mul_one 1
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, mul_inv_cancel₀ (hp _), Complex.ofReal_one]
end Formalism.FourierDecayAlt.P.B2
