-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.conj_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:55.963927+00:00
-- url     : https://prove2.me/submissions/a3ecac57-89e3-4dfc-83db-08475c46e79d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) = ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  rw [map_sum, Finset.sum_comm]
  simp only [map_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro y hy
  rw [map_mul, map_mul, Complex.conj_conj, ← hh y hy x hx]; ring
end Formalism.FourierDecayAlt.P.Jx8
