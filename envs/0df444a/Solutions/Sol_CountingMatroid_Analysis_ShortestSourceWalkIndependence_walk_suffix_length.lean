-- Prove2me | solution 1 for CountingMatroid.Analysis.ShortestSourceWalkIndependence.walk_suffix_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:51:10.861123+00:00
-- url     : https://prove2.me/submissions/bede9c1a-9016-4ebf-950a-ab82141c5e60

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
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
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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

namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace Arlib
end Arlib
set_option autoImplicit false

/-! The first-matroid half of shortest-path augmentation. Fundamental circuits
of later outside vertices avoid all earlier removed inside vertices, since such
membership would give a shorter source walk. -/
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open scoped symmDiff

/-- INTERNAL: Every vertex of a source walk has a source-walk suffix of no
larger length. -/
theorem solution {n : ℕ} {g : ExchangeGraph n} {p : List (Fin n)}
    (hw : SourceWalk g p) : ∀ v ∈ p, ∃ q, SourceWalk g (v :: q) ∧
      (v :: q).length ≤ p.length := by
  induction hw with
  | source u hs =>
    intro v hv
    have : v = u := by simpa using hv
    subst v
    exact ⟨[], .source u hs, le_rfl⟩
  | step u w tail hw he ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨u :: tail, .step u v tail hw he, le_rfl⟩
    · obtain ⟨q, hq, hlen⟩ := ih v hv
      exact ⟨q, hq, by simp only [List.length_cons] at *; omega⟩
