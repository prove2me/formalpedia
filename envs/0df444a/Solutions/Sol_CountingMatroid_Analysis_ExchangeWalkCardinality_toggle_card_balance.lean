-- Prove2me | solution 1 for CountingMatroid.Analysis.ExchangeWalkCardinality.toggle_card_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:50:55.347021+00:00
-- url     : https://prove2.me/submissions/f94d2be2-e362-4784-ac6f-55e2a27f508d

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

namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace Arlib
end Arlib
set_option autoImplicit false

/-! Cardinality of the symmetric difference with a simple alternating
source-to-sink exchange walk. This argument uses no matroid exchange theorem. -/
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: A list of distinct toggles removes its original inside vertices
and adds its original outside vertices, with no double toggles. -/
theorem solution {n : ℕ} (p : List (Fin n)) (I : Finset (Fin n))
    (hp : p.Nodup) :
    (p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I).card +
      (p.filter (fun i => decide (i ∈ I))).length =
    I.card + (p.filter (fun i => decide (i ∉ I))).length := by
  classical
  induction p generalizing I with
  | nil => simp
  | cons i p ih =>
    obtain ⟨hi, hp⟩ := List.nodup_cons.mp hp
    by_cases hiI : i ∈ I
    · have hinside : p.filter (fun j => decide (j ∈ I.erase i)) =
          p.filter (fun j => decide (j ∈ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have houtside : p.filter (fun j => decide (j ∉ I.erase i)) =
          p.filter (fun j => decide (j ∉ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have h := ih (I.erase i) hp
      rw [hinside, houtside] at h
      have hcard := Finset.card_erase_add_one hiI
      simp only [List.foldl_cons, List.filter_cons, hiI, not_true_eq_false, decide_true, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] 
      omega
    · have hinside : p.filter (fun j => decide (j ∈ insert i I)) =
          p.filter (fun j => decide (j ∈ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have houtside : p.filter (fun j => decide (j ∉ insert i I)) =
          p.filter (fun j => decide (j ∉ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have h := ih (insert i I) hp
      rw [hinside, houtside, Finset.card_insert_of_notMem hiI] at h
      simp only [List.foldl_cons, List.filter_cons, hiI, not_false_eq_true, decide_true, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      omega
