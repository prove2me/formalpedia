-- Prove2me | solution 1 for CountingMatroid.Analysis.FrozenPathTable.frozen_paths_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:08:29.34946+00:00
-- url     : https://prove2.me/submissions/c43bb42c-2381-4380-873a-97291e03b807

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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearch_tabulate_val

namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace Arlib
end Arlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The frozen BFS table certificate, before the final sink selection.
First discovery and bounded-distance completeness establish simple, globally
shortest recorded source walks. Thus the representation cap discards no vertex. -/
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FrozenPathTable
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: After the frozen layers, every recorded path is a simple source
walk at its indexed endpoint, and every source walk of at most `n` vertices
has a recorded path no longer than it.
TEXLINE: main.tex:283-289 -/
theorem solution {n : ℕ} (g : ExchangeGraph n) :
    let paths := (Arlib.Computation.Charged.foldl
      (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
      (initialPaths g).val).val
    (∀ v p, paths v = some p →
      SourceWalk g p ∧ (∃ tail, p = v :: tail) ∧ p.Nodup ∧ p.length ≤ n) ∧
    (∀ v tail, SourceWalk g (v :: tail) → (v :: tail).length ≤ n →
      ∃ p, paths v = some p ∧ p.length ≤ (v :: tail).length) := by
  classical
  have hsuffix (p : List (Fin n)) (hw : SourceWalk g p) :
      ∀ v ∈ p, ∃ tail, SourceWalk g (v :: tail) ∧ (v :: tail).length ≤ p.length := by
    induction hw with
    | source u hu =>
      intro v hv
      simp only [List.mem_singleton] at hv
      subst v
      exact ⟨[], SourceWalk.source u hu, le_rfl⟩
    | step u w tail hw he ih =>
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        exact ⟨u :: tail, SourceWalk.step u w tail hw he, le_rfl⟩
      · obtain ⟨rest, hr, hl⟩ := ih v hv
        exact ⟨rest, hr, hl.trans (by simp)⟩
  let Entry (k : ℕ) (v : Fin n) (p : List (Fin n)) : Prop :=
    SourceWalk g p ∧ (∃ tail, p = v :: tail) ∧ p.Nodup ∧ p.length ≤ k + 1 ∧
      ∀ tail, SourceWalk g (v :: tail) → p.length ≤ (v :: tail).length
  let Inv (k : ℕ) (previous : Paths n) : Prop :=
    (∀ v p, previous v = some p → Entry k v p) ∧
      (∀ v tail, SourceWalk g (v :: tail) → (v :: tail).length ≤ k + 1 →
        ∃ p, previous v = some p)
  have hinitial : Inv 0 (initialPaths g).val := by
    constructor
    · intro v p hp
      simp only [initialPaths, tabulate_val] at hp
      cases ht : (g.terminals v).1 <;> simp [ht] at hp
      subst p
      exact ⟨SourceWalk.source v ht, ⟨[], rfl⟩, by simp, by simp,
        fun tail _ => by simp⟩
    · intro v tail hw hl
      have htail : tail = [] := by
        simpa using hl
      subst tail
      have ht : (g.terminals v).1 = true := by cases hw; assumption
      exact ⟨[v], by simp [initialPaths, tabulate_val, ht]⟩
  have hnew (k : ℕ) (previous : Paths n) (hinv : Inv k previous)
      (v u : Fin n) (p : List (Fin n)) (hmissing : previous v = none)
      (hp : previous u = some p) (he : g.edges u v = true) :
      Entry (k + 1) v (v :: p) ∧ (v :: p).length ≤ n := by
    obtain ⟨hw, ⟨tail, hhead⟩, hd, hl, hmin⟩ := hinv.1 u p hp
    have hnot : v ∉ p := by
      intro hv
      obtain ⟨rest, hr, hrl⟩ := hsuffix p hw v hv
      obtain ⟨q, hq⟩ := hinv.2 v rest hr (hrl.trans hl)
      rw [hmissing] at hq
      cases hq
    have hdup : (v :: p).Nodup := List.nodup_cons.mpr ⟨hnot, hd⟩
    have hwalk : SourceWalk g (v :: p) := by
      rw [hhead]
      exact SourceWalk.step u v tail (hhead ▸ hw) he
    have hlen : (v :: p).length ≤ k + 1 + 1 := by simp only [List.length_cons]; omega
    refine ⟨⟨hwalk, ⟨p, rfl⟩, hdup, hlen, ?_⟩, ?_⟩
    · intro rest hr
      have hlong : ¬ (v :: rest).length ≤ k + 1 := by
        intro hrl
        obtain ⟨q, hq⟩ := hinv.2 v rest hr hrl
        rw [hmissing] at hq
        cases hq
      omega
    · simpa only [Fintype.card_fin] using hdup.length_le_card
  have hflagstep (previous : Paths n) (v u : Fin n)
      (found : Option (List (Fin n))) :
      (predecessorStep g previous v found u).val.isSome = true ↔
        found.isSome = true ∨ (previous u).isSome = true ∧ g.edges u v = true := by
    cases found <;> cases hp : previous u <;> cases he : g.edges u v <;>
      simp [predecessorStep, CountingMatroid.Model.Operations.isSome, hp, he]
  have hflagscan (previous : Paths n) (v : Fin n) (indices : List (Fin n))
      (found : Option (List (Fin n))) :
      (Arlib.Computation.Charged.foldl (predecessorStep g previous v)
        indices found).val.isSome = true ↔
      found.isSome = true ∨ ∃ u ∈ indices,
        (previous u).isSome = true ∧ g.edges u v = true := by
    induction indices generalizing found with
    | nil => simp
    | cons u indices ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, hflagstep]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
  -- The successor proof uses first discovery to exclude a repeated endpoint
  -- before rewriting take n away; ordinary entry soundness is insufficient.
  have hrelax (k : ℕ) (previous : Paths n) (hinv : Inv k previous) :
      Inv (k + 1) (relaxPaths g previous).val := by
    constructor
    · intro v p hp
      simp only [relaxPaths, tabulate_val] at hp
      cases hold : previous v with
      | some old =>
        simp [relaxVertex, CountingMatroid.Model.Operations.isSome, hold] at hp
        subst p
        obtain ⟨hw, he, hd, hl, hm⟩ := hinv.1 v old hold
        exact ⟨hw, he, hd, by omega, hm⟩
      | none =>
        have hstep (found : Option (List (Fin n))) (u : Fin n)
            (hf : ∀ q, found = some q → Entry (k + 1) v q) :
            ∀ q, (predecessorStep g previous v found u).val = some q →
              Entry (k + 1) v q := by
          intro q hq
          cases found with
          | some r =>
            simp [predecessorStep, CountingMatroid.Model.Operations.isSome] at hq
            subst q
            exact hf r rfl
          | none =>
            cases hu : previous u with
            | none =>
              simp [predecessorStep, CountingMatroid.Model.Operations.isSome, hu] at hq
            | some r =>
              cases he : g.edges u v with
              | false =>
                simp [predecessorStep, CountingMatroid.Model.Operations.isSome,
                  hu, he] at hq
              | true =>
                have hr := hnew k previous hinv v u r hold hu he
                simp [predecessorStep, CountingMatroid.Model.Operations.isSome,
                  hu, he, List.take_of_length_le hr.2] at hq
                subst q
                exact hr.1
        have hscan (indices : List (Fin n)) (found : Option (List (Fin n)))
            (hf : ∀ q, found = some q → Entry (k + 1) v q) :
            ∀ q, (Arlib.Computation.Charged.foldl (predecessorStep g previous v)
              indices found).val = some q → Entry (k + 1) v q := by
          induction indices generalizing found with
          | nil => exact hf
          | cons u indices ih =>
            rw [Arlib.Computation.Charged.val_foldl_cons]
            exact ih _ (hstep found u hf)
        apply hscan (List.finRange n) none (by simp) p
        simpa [relaxVertex, CountingMatroid.Model.Operations.isSome, hold] using hp
    · intro v tail hw hl
      cases hold : previous v with
      | some p =>
        exact ⟨p, by simp [relaxPaths, tabulate_val, relaxVertex,
          CountingMatroid.Model.Operations.isSome, hold]⟩
      | none =>
        have hflag : ((relaxPaths g previous).val v).isSome = true := by
          simp only [relaxPaths, tabulate_val]
          simp only [relaxVertex, Arlib.Computation.Charged.val_bind,
            Arlib.Computation.Charged.val_opMany, hold,
            CountingMatroid.Model.Operations.isSome, Arlib.Computation.Charged.val_op,
            Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          apply (hflagscan previous v (List.finRange n) none).mpr
          right
          cases hw with
          | source v ht =>
            obtain ⟨p, hp⟩ := hinv.2 v [] (SourceWalk.source v ht) (by simp)
            rw [hold] at hp
            cases hp
          | step u v rest hu he =>
            obtain ⟨p, hp⟩ := hinv.2 u rest hu (by simp only [List.length_cons] at hl ⊢; omega)
            exact ⟨u, List.mem_finRange u, by simp [hp], he⟩
        cases hv : (relaxPaths g previous).val v with
        | none => simp [hv] at hflag
        | some p => exact ⟨p, rfl⟩
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
    (Arlib.Computation.Charged.foldl
      (fun paths (_ : ℕ) => relaxPaths g paths) (List.range k)
      (initialPaths g).val).val
  have hlayers_succ (k : ℕ) : layers (k + 1) = (relaxPaths g (layers k)).val := by
    dsimp only [layers]
    rw [List.range_succ, happend]
    simp only [Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_foldl_nil]
  have hlayers : ∀ k, Inv k (layers k) := by
    intro k
    induction k with
    | zero => exact hinitial
    | succ k ih =>
      rw [hlayers_succ]
      exact hrelax k (layers k) ih
  have hfinal := hlayers n
  constructor
  · intro v p hp
    obtain ⟨hw, he, hd, _, _⟩ := hfinal.1 v p hp
    exact ⟨hw, he, hd, by simpa only [Fintype.card_fin] using hd.length_le_card⟩
  · intro v tail hw hl
    obtain ⟨p, hp⟩ := hfinal.2 v tail hw (by omega)
    exact ⟨p, hp, (hfinal.1 v p hp).2.2.2.2 tail hw⟩
