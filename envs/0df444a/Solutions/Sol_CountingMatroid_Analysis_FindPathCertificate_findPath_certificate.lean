-- Prove2me | solution 1 for CountingMatroid.Analysis.FindPathCertificate.findPath_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:40:45.22451+00:00
-- url     : https://prove2.me/submissions/bc4124b1-af24-454f-8eb5-b230e9246976

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
import Theorems.Thm_CountingMatroid_Analysis_FrozenPathTable_frozen_paths_certificate

namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace Arlib
end Arlib
set_option autoImplicit false

/-! Algorithmic half of successful augmentation, independent of matroid axioms.
The frozen BFS table certificate supplies valid simple source walks and
bounded-distance optimality. The final sink fold preserves validity and
selects a globally shortest source-to-sink walk. Both list caps are harmless. -/
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FindPathCertificate
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: The concrete frozen-layer search returns a shortest simple
source-to-sink reverse walk, so neither list cap discards a vertex.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n))
    (hp : (findPath g).val = some p) : ShortestCertificate g p := by
  have hstep (paths : Paths n) (best : Option (List (Fin n))) (i : Fin n)
      (hb : ∀ q, best = some q → q.length ≤ n) :
      ∀ q, (sinkStep g paths best i).val = some q → q.length ≤ n := by
    intro q hq
    cases ht : (g.terminals i).2 <;> cases hv : paths i <;> cases best <;>
      simp [sinkStep, ht, hv, CountingMatroid.Model.Operations.lessThan] at hq hb
    all_goals first
      | (subst q; exact hb)
      | (subst q; simp only [List.length_take]; exact Nat.min_le_left _ _)
      | (split at hq <;> simp only [Arlib.Computation.Charged.val_pure,
          Option.some.injEq] at hq <;> subst q
         · simp only [List.length_take]; exact Nat.min_le_left _ _
         · exact hb)
  have hfold (paths : Paths n) (indices : List (Fin n))
      (best : Option (List (Fin n)))
      (hb : ∀ q, best = some q → q.length ≤ n) :
      ∀ q, (Arlib.Computation.Charged.foldl (sinkStep g paths) indices best).val =
        some q → q.length ≤ n := by
    induction indices generalizing best with
    | nil => exact hb
    | cons i indices ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hstep paths best i hb)
  have hlength : p.length ≤ n := by
    unfold findPath at hp
    simp only [Arlib.Computation.Charged.val_bind] at hp
    exact hfold _ _ none (by simp) p hp
  let paths : Paths n := (Arlib.Computation.Charged.foldl
    (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
    (initialPaths g).val).val
  have hpaths := CountingMatroid.Analysis.FrozenPathTable.frozen_paths_certificate g
  change (∀ v q, paths v = some q →
      SourceWalk g q ∧ (∃ tail, q = v :: tail) ∧ q.Nodup ∧ q.length ≤ n) ∧
    (∀ v tail, SourceWalk g (v :: tail) → (v :: tail).length ≤ n →
      ∃ q, paths v = some q ∧ q.length ≤ (v :: tail).length) at hpaths
  let Good (q : List (Fin n)) : Prop :=
    AugmentingWalk g q ∧ q.Nodup ∧ q.length ≤ n
  have hentry (i : Fin n) (q : List (Fin n))
      (hv : paths i = some q) (ht : (g.terminals i).2 = true) : Good q := by
    obtain ⟨hw, ⟨tail, he⟩, hd, hl⟩ := hpaths.1 i q hv
    exact ⟨⟨hw, i, tail, he, ht⟩, hd, hl⟩
  have hsoundstep (best : Option (List (Fin n))) (i : Fin n)
      (hb : ∀ q, best = some q → Good q) :
      ∀ q, (sinkStep g paths best i).val = some q → Good q := by
    intro q hq
    cases ht : (g.terminals i).2 with
    | false =>
      simp [sinkStep, ht] at hq
      exact hb q hq
    | true =>
      cases hv : paths i with
      | none =>
        simp [sinkStep, ht, hv] at hq
        exact hb q hq
      | some r =>
        have hr := hentry i r hv ht
        have htake : r.take n = r := List.take_of_length_le hr.2.2
        cases best with
        | none =>
          simp [sinkStep, ht, hv, htake] at hq
          subst q
          exact hr
        | some s =>
          have hs := hb s rfl
          simp [sinkStep, ht, hv, htake,
            CountingMatroid.Model.Operations.lessThan,
            List.take_of_length_le hs.2.2] at hq
          by_cases hlt : r.length < s.length
          · simp [hlt] at hq
            subst q
            exact hr
          · simp [hlt] at hq
            subst q
            exact hs
  have hvalue (best : Option (List (Fin n))) (i : Fin n)
      (hb : ∀ q, best = some q → Good q) :
      (sinkStep g paths best i).val =
        if (g.terminals i).2 then
          match paths i with
          | none => best
          | some r => match best with
            | none => some r
            | some s => if r.length < s.length then some r else some s
        else best := by
    cases ht : (g.terminals i).2 <;> cases hv : paths i
    all_goals try { simp [sinkStep, ht, hv] }
    rename_i r
    have hr := hentry i r hv ht
    cases best with
    | none => simp [sinkStep, ht, hv, List.take_of_length_le hr.2.2]
    | some s =>
      have hs := hb s rfl
      simp [sinkStep, ht, hv, List.take_of_length_le hr.2.2,
        List.take_of_length_le hs.2.2, CountingMatroid.Model.Operations.lessThan]
      by_cases hlt : r.length < s.length <;> simp [hlt]
  have hstep_old (q : List (Fin n)) (i : Fin n) (hq : Good q) :
      ∃ r, (sinkStep g paths (some q) i).val = some r ∧ r.length ≤ q.length := by
    rw [hvalue (some q) i (by intro s hs; cases hs; exact hq)]
    cases (g.terminals i).2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ⟨q, rfl, le_rfl⟩
    · cases hv : paths i with
      | none => exact ⟨q, rfl, le_rfl⟩
      | some s =>
        by_cases hlt : s.length < q.length
        · exact ⟨s, if_pos hlt, Nat.le_of_lt hlt⟩
        · exact ⟨q, if_neg hlt, le_rfl⟩
  have hstep_entry (best : Option (List (Fin n))) (i : Fin n)
      (hb : ∀ q, best = some q → Good q) (q : List (Fin n))
      (hv : paths i = some q) (ht : (g.terminals i).2 = true) :
      ∃ r, (sinkStep g paths best i).val = some r ∧ r.length ≤ q.length := by
    rw [hvalue best i hb, ht, hv]
    simp only [↓reduceIte]
    cases best with
    | none => exact ⟨q, rfl, le_rfl⟩
    | some s =>
      by_cases hlt : q.length < s.length
      · exact ⟨q, if_pos hlt, le_rfl⟩
      · exact ⟨s, if_neg hlt, Nat.le_of_not_gt hlt⟩
  have hsoundfold (indices : List (Fin n)) (best : Option (List (Fin n)))
      (hb : ∀ q, best = some q → Good q) :
      ∀ q, (Arlib.Computation.Charged.foldl (sinkStep g paths) indices best).val =
        some q → Good q := by
    induction indices generalizing best with
    | nil => exact hb
    | cons i indices ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hsoundstep best i hb)
  have hfold_old (indices : List (Fin n)) (best : Option (List (Fin n)))
      (hb : ∀ q, best = some q → Good q) (q : List (Fin n))
      (hq : best = some q) :
      ∃ r, (Arlib.Computation.Charged.foldl (sinkStep g paths) indices best).val =
        some r ∧ r.length ≤ q.length := by
    induction indices generalizing best q with
    | nil => exact ⟨q, hq, le_rfl⟩
    | cons i indices ih =>
      subst best
      obtain ⟨s, hs, hsq⟩ := hstep_old q i (hb q rfl)
      obtain ⟨r, hr, hrs⟩ := ih _ (hsoundstep _ i hb) s hs
      exact ⟨r, by rw [Arlib.Computation.Charged.val_foldl_cons]; exact hr,
        hrs.trans hsq⟩
  have hfold_entry (indices : List (Fin n)) (best : Option (List (Fin n)))
      (hb : ∀ q, best = some q → Good q) (i : Fin n) (hi : i ∈ indices)
      (q : List (Fin n)) (hv : paths i = some q) (ht : (g.terminals i).2 = true) :
      ∃ r, (Arlib.Computation.Charged.foldl (sinkStep g paths) indices best).val =
        some r ∧ r.length ≤ q.length := by
    induction indices generalizing best with
    | nil => simp at hi
    | cons j indices ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      have hb' := hsoundstep best j hb
      rcases List.mem_cons.mp hi with hij | hi
      · subst j
        obtain ⟨s, hs, hsq⟩ := hstep_entry best i hb q hv ht
        obtain ⟨r, hr, hrs⟩ := hfold_old indices _ hb' s hs
        exact ⟨r, hr, hrs.trans hsq⟩
      · exact ih _ hb' hi
  have hp' : (Arlib.Computation.Charged.foldl (sinkStep g paths)
      (List.finRange n) none).val = some p := by
    simpa only [findPath, Arlib.Computation.Charged.val_bind] using hp
  have hgood := hsoundfold (List.finRange n) none (by simp) p hp'
  refine ⟨hgood.1, hgood.2.1, hlength, ?_⟩
  intro q hq
  by_cases hqn : q.length ≤ n
  · obtain ⟨hw, v, tail, rfl, ht⟩ := hq
    obtain ⟨s, hs, hsq⟩ := hpaths.2 v tail hw hqn
    obtain ⟨r, hr, hrs⟩ := hfold_entry (List.finRange n) none (by simp)
      v (List.mem_finRange v) s hs ht
    rw [hp'] at hr
    cases hr
    exact hrs.trans hsq
  · exact hlength.trans (Nat.le_of_not_ge hqn)
