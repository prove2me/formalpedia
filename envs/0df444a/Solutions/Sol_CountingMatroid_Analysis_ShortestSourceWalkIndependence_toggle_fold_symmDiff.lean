-- Prove2me | solution 1 for CountingMatroid.Analysis.ShortestSourceWalkIndependence.toggle_fold_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:51:52.193776+00:00
-- url     : https://prove2.me/submissions/6b2cab9e-dcf8-4aa8-a985-b32daf66e2a6

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

/-- INTERNAL: Distinct executable toggles equal symmetric difference with the
path's vertex set. -/
theorem solution {n : ℕ} (I : Finset (Fin n)) (p : List (Fin n))
    (hp : p.Nodup) :
    p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I =
      I ∆ p.toFinset := by
  classical
  induction p generalizing I with
  | nil => ext w; simp [Finset.mem_symmDiff]
  | cons v p ih =>
    obtain ⟨hv, hp⟩ := List.nodup_cons.mp hp
    rw [List.foldl_cons, ih _ hp]
    ext w
    by_cases hw : w = v
    · subst w
      by_cases hvi : v ∈ I <;> simp [Finset.mem_symmDiff, hvi, hv]
    · by_cases hvi : v ∈ I <;> simp [Finset.mem_symmDiff, hvi, hw]
