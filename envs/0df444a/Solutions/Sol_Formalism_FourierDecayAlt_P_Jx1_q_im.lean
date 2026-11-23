-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.q_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:14.800358+00:00
-- url     : https://prove2.me/submissions/19bae44a-9f73-49fb-be79-8daddff9861c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h
end Formalism.FourierDecayAlt.P.Jx1
