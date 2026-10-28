-- Prove2me | solution 1 for CountingMatroid.Analysis.NoPathSeparator.no_path_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:08:29.164104+00:00
-- url     : https://prove2.me/submissions/e5e18641-93da-4322-aff5-46d471771501

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val

namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Graph-theoretic correctness of the capped synchronous search in
`IntersectionSearch`. The separator is a set of vertices containing every
source, closed under directed edges, and containing no sink. This file does
not use matroid axioms or assume a mathematical intersection algorithm.
-/

namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.NoPathSeparator

open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: A failed capped BFS supplies a directed separator. On a graph
with `n` vertices, `n` frozen layers exhaust source reachability; capped path
payloads do not change the Boolean discovery flags.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (g : ExchangeGraph n)
    (hnone : (findPath g).val = none) :
    ∃ R : Finset (Fin n),
      (∀ i, (g.terminals i).1 = true → i ∈ R) ∧
      (∀ u v, u ∈ R → g.edges u v = true → v ∈ R) ∧
      (∀ i, i ∈ R → (g.terminals i).2 = false) := by
  classical
  have hstep (previous : Paths n) (v u : Fin n) (found : Option (List (Fin n))) :
      (predecessorStep g previous v found u).val.isSome = true ↔
        found.isSome = true ∨ (previous u).isSome = true ∧ g.edges u v = true := by
    cases found <;> cases hp : previous u <;> cases he : g.edges u v <;>
      simp [predecessorStep, CountingMatroid.Model.Operations.isSome, hp, he]
  have hscan (previous : Paths n) (v : Fin n) (l : List (Fin n))
      (found : Option (List (Fin n))) :
      (Arlib.Computation.Charged.foldl (predecessorStep g previous v) l found).val.isSome = true ↔
        found.isSome = true ∨ ∃ u ∈ l, (previous u).isSome = true ∧ g.edges u v = true := by
    induction l generalizing found with
    | nil => simp
    | cons u l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, hstep]
      simp only [List.mem_cons]
      aesop
  have hrelax (previous : Paths n) (v : Fin n) :
      ((relaxPaths g previous).val v).isSome = true ↔
        (previous v).isSome = true ∨ ∃ u, (previous u).isSome = true ∧ g.edges u v = true := by
    simp only [relaxPaths, tabulate_val]
    cases hp : previous v with
    | none =>
      simpa [relaxVertex, CountingMatroid.Model.Operations.isSome, hp] using
        hscan previous v (List.finRange n) none
    | some p => simp [relaxVertex, CountingMatroid.Model.Operations.isSome, hp]
  have hinitial (v : Fin n) : ((initialPaths g).val v).isSome = true ↔
      (g.terminals v).1 = true := by
    simp only [initialPaths, tabulate_val]
    cases h : (g.terminals v).1 <;> simp [h]
  have hsinkstep (paths : Paths n) (best : Option (List (Fin n))) (v : Fin n) :
      (sinkStep g paths best v).val = none ↔
        best = none ∧ ((g.terminals v).2 = true → paths v = none) := by
    cases best <;> cases hp : paths v <;> cases ht : (g.terminals v).2 <;>
      simp [sinkStep, CountingMatroid.Model.Operations.lessThan, hp, ht] <;>
      split <;> simp
  have hsinkscan (paths : Paths n) (l : List (Fin n))
      (best : Option (List (Fin n))) :
      (Arlib.Computation.Charged.foldl (sinkStep g paths) l best).val = none ↔
        best = none ∧ ∀ v ∈ l, (g.terminals v).2 = true → paths v = none := by
    induction l generalizing best with
    | nil => simp
    | cons v l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, hsinkstep]
      constructor
      · rintro ⟨⟨hb, hv⟩, hl⟩
        exact ⟨hb, fun u hu => (List.mem_cons.mp hu).elim (fun h => h ▸ hv) (hl u)⟩
      · rintro ⟨hb, hl⟩
        exact ⟨⟨hb, hl v (List.mem_cons_self)⟩,
          fun u hu => hl u (List.mem_cons_of_mem v hu)⟩
  have happend (l₁ l₂ : List ℕ) (previous : Paths n) :
      (Arlib.Computation.Charged.foldl (fun paths (_ : ℕ) => relaxPaths g paths)
        (l₁ ++ l₂) previous).val =
      (Arlib.Computation.Charged.foldl (fun paths (_ : ℕ) => relaxPaths g paths)
        l₂ (Arlib.Computation.Charged.foldl
          (fun paths (_ : ℕ) => relaxPaths g paths) l₁ previous).val).val := by
    induction l₁ generalizing previous with
    | nil => simp
    | cons a l ih =>
      simp only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
      exact ih _
  let layers (k : ℕ) : Paths n :=
    (Arlib.Computation.Charged.foldl (fun paths (_ : ℕ) => relaxPaths g paths)
      (List.range k) (initialPaths g).val).val
  have hlayers (k : ℕ) : layers (k + 1) = (relaxPaths g (layers k)).val := by
    dsimp only [layers]
    rw [List.range_succ, happend]
    simp only [Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_foldl_nil]
  let reach (k : ℕ) : Finset (Fin n) := Finset.univ.filter
    (fun i => (layers k i).isSome)
  have hflag (k : ℕ) (v : Fin n) :
      v ∈ reach k ↔ (layers k v).isSome = true := by
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
  have hreachsucc (k : ℕ) (v : Fin n) :
      v ∈ reach (k + 1) ↔ v ∈ reach k ∨ ∃ u ∈ reach k, g.edges u v = true := by
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and, hlayers]
    exact hrelax (layers k) v
  have hmono : Monotone reach := monotone_nat_of_le_succ
    (fun k v hv => (hreachsucc k v).mpr (Or.inl hv))
  have hstable (k : ℕ) (hk : reach k = reach (k + 1)) :
      ∀ t, reach (k + t) = reach k := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      ext v
      rw [Nat.add_succ, hreachsucc, ih, ← hreachsucc, ← hk]
  have hfixed : reach n = reach (n + 1) := by
    by_contra hne
    have hstrict (k : ℕ) (hkn : k ≤ n) : reach k ⊂ reach (k + 1) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hmono (Nat.le_succ k), ?_⟩
      intro hk
      have ha := hstable k hk (n - k)
      have hb := hstable k hk (n + 1 - k)
      rw [Nat.add_sub_of_le hkn] at ha
      rw [Nat.add_sub_of_le (by omega : k ≤ n + 1)] at hb
      exact hne (ha.trans hb.symm)
    have hcard (k : ℕ) (hk : k ≤ n + 1) : k ≤ (reach k).card := by
      induction k with
      | zero => omega
      | succ k ih =>
        have hprev := ih (by omega)
        have hgrowth := Finset.card_lt_card (hstrict k (by omega))
        omega
    have hc := hcard (n + 1) (by omega)
    have hbound := Finset.card_le_univ (reach (n + 1))
    simp only [Fintype.card_fin] at hbound
    omega

  simp only [findPath, Arlib.Computation.Charged.val_bind] at hnone
  let paths := (Arlib.Computation.Charged.foldl
    (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
    (initialPaths g).val).val
  have hnosink : ∀ v, (g.terminals v).2 = true → paths v = none := by
    have h := (hsinkscan paths (List.finRange n) none).mp hnone
    exact fun v => h.2 v (List.mem_finRange v)
  refine ⟨Finset.univ.filter (fun i => (paths i).isSome), ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hzero : i ∈ reach 0 := by
      apply (hflag 0 i).mpr
      simpa only [layers, List.range_zero, Arlib.Computation.Charged.val_foldl_nil] using
        (hinitial i).mpr hi
    exact (hflag n i).mp (hmono (Nat.zero_le n) hzero)
  · intro u v hu huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    apply (hflag n v).mp
    rw [hfixed]
    apply (hreachsucc n v).mpr
    exact Or.inr ⟨u, (hflag n u).mpr hu, huv⟩
  · intro i hi
    apply Bool.eq_false_iff.mpr
    intro ht
    have hpath := hnosink i ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpath,
      Option.isSome_none, Bool.false_eq_true] at hi
