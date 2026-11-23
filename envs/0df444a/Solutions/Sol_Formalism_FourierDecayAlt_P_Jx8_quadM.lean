-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.quadM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:22.312837+00:00
-- url     : https://prove2.me/submissions/833233fe-43f3-4145-9e3e-989a4a5eb70b

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
theorem _root_.solution (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro y _
  simp only [RCLike.star_def]; ring
end Formalism.FourierDecayAlt.P.Jx8
