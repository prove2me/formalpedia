-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.quad1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:56.514786+00:00
-- url     : https://prove2.me/submissions/1278669c-253f-411a-8c50-dc22033cc3be

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
theorem _root_.solution [DecidableEq α] (F : Finset α) (k : α → α → ℂ) (x : α) (hx : x ∈ F) :
    ∑ u ∈ F, ∑ v ∈ F, (if u = x then (1 : ℂ) else 0) * conj (if v = x then (1 : ℂ) else 0) * k u v = k x x := by
  rw [Finset.sum_eq_single x (fun u _ hu => by simp [hu]) (fun h => absurd hx h)]
  rw [Finset.sum_eq_single x (fun v _ hv => by simp [hv]) (fun h => absurd hx h)]
  simp
end Formalism.FourierDecayAlt.P.Jx8
