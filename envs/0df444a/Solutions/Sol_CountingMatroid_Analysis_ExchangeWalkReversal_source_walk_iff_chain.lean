-- Prove2me | solution 1 for CountingMatroid.Analysis.ExchangeWalkReversal.source_walk_iff_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:51:05.779016+00:00
-- url     : https://prove2.me/submissions/310eab40-17ea-4d42-9d9f-95b32553973a

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
set_option autoImplicit false

/-! Reversing an exchange graph interchanges its sources and sinks. Reverse
list paths then satisfy the same augmentation and shortestness predicates. -/
namespace CountingMatroid.Analysis.ExchangeWalkReversal
end CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: SourceWalk is the ordinary adjacent-edge chain together with
its source flag at the last vertex of the reverse list. -/
theorem solution {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) :
    SourceWalk g p ↔
      p.IsChain (fun v u => g.edges u v = true) ∧
        ∃ v, p.getLast? = some v ∧ (g.terminals v).1 = true := by
  constructor
  · intro hw
    induction hw with
    | source v hs => exact ⟨by simp, v, rfl, hs⟩
    | step u v tail hw he ih =>
      exact ⟨List.isChain_cons_cons.mpr ⟨he, ih.1⟩, by
        simpa only [List.getLast?_cons_cons] using ih.2⟩
  · induction p with
    | nil => simp
    | cons v p ih =>
      cases p with
      | nil =>
        rintro ⟨_, w, heq, hs⟩
        have : v = w := Option.some.inj heq
        subst w
        exact .source v hs
      | cons u tail =>
        rintro ⟨hchain, hlast⟩
        obtain ⟨he, hchain⟩ := List.isChain_cons_cons.mp hchain
        apply SourceWalk.step u v tail
        · apply ih
          exact ⟨hchain, by simpa only [List.getLast?_cons_cons] using hlast⟩
        · exact he
