-- Prove2me | solution 1 for D1Bound5.pairClosure_of_witness_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:58.518544+00:00
-- url     : https://prove2.me/submissions/45a5f41d-c309-4350-af57-ff91fb4a586b

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_pairMutation_eq_supplied_roots

section
namespace D1Bound5
open QuadInt















theorem pairWitnessCandidateCovered_of_checked {tau nu : ℤ}
    (bound : ℤ) (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (hcheck : pairWitnessCandidateCoveredBool bound vertices w = true)
    (hbound : w.norm ≤ bound) : w ∈ vertices := by
  simpa [pairWitnessCandidateCoveredBool, hbound] using hcheck

/-- The witness certificate supplies exactly the closure hypothesis used by
the accepted full-ring descent completeness theorem. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (hcheck : pairClosureWitnessBool a b r0 bound vertices witnesses = true)
    {z w : QuadInt tau nu} (hz : z ∈ vertices)
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z)
    (hbound : w.norm ≤ bound) : w ∈ vertices := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hdata : r0 * r0 = a * b + 1 ∧
      witnesses.map PairRootWitness.vertex = vertices := of_decide_eq_true hparts.1
  have hzmap : z ∈ witnesses.map PairRootWitness.vertex := by rwa [hdata.2]
  obtain ⟨v, hv, hvz⟩ := List.mem_map.mp hzmap
  have hc := List.all_eq_true.mp hparts.2 v hv
  have hvparts := Bool.and_eq_true_iff.mp hc
  have hroots : v.leftRoot * v.leftRoot = a * v.vertex + 1 ∧
      v.rightRoot * v.rightRoot = b * v.vertex + 1 := of_decide_eq_true hvparts.1
  have hneighbors := Bool.and_eq_true_iff.mp hvparts.2
  have hw' : w = pairMutationPlus a b v.vertex ∨
      w = pairMutationMinus a b v.vertex := by simpa only [hvz] using hw
  rcases pairMutation_eq_supplied_roots hd a b v.vertex r0 v.leftRoot v.rightRoot
    hdata.1 hroots.1 hroots.2 hw' with hplus | hminus
  · rw [hplus] at hbound ⊢
    exact pairWitnessCandidateCovered_of_checked bound vertices _ hneighbors.1 hbound
  · rw [hminus] at hbound ⊢
    exact pairWitnessCandidateCovered_of_checked bound vertices _ hneighbors.2 hbound



end D1Bound5
end
