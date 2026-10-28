-- Prove2me | solution 1 for CountingMatroid.Analysis.GreedyRankCorrect.greedyRank_eq_eRk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:51:17.114027+00:00
-- url     : https://prove2.me/submissions/7fd81ea6-aa28-4b33-b8c6-67550033e0c2

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
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

namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.GreedyRankCorrect

open CountingMatroid.Model

/-- INTERNAL: The charged greedy scan computes the matroid rank from an exact
independence oracle. The cast states the equality in Mathlib's `ℕ∞` rank type.
TEXLINE: main.tex:247-249,1333-1346 -/
theorem solution {n : ℕ} (M : Matroid (Fin n))
    (o : IndependenceOracle n) (hfull : M.E = Set.univ)
    (hexact : ExactOracle M o) (which : Bool) (A : Finset (Fin n)) :
    ((CountingMatroid.Model.Subroutines.greedyRank which o A).val : ℕ∞) =
      M.eRk (A : Set (Fin n)) := by
  classical
  have hq (T : Finset (Fin n)) :
      o (fun j => decide (j ∈ T)) = decide (M.Indep (T : Set (Fin n))) := by
    rw [hexact]
    congr 1
    ext
    simp [decode]
  let step : (Finset (Fin n) × ℕ) → Fin n →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell (Finset (Fin n) × ℕ) := fun acc i => do
    let present ← CountingMatroid.Model.Operations.containsElement A i
    if present then
      let candidate ← CountingMatroid.Model.Operations.insertElement acc.1 i
      let q ← CountingMatroid.Model.Operations.encodeQuery candidate
      let independent ← CountingMatroid.Model.Operations.oracleQuery which o q
      if independent then
        let size ← CountingMatroid.Model.Operations.successor acc.2
        pure (candidate, size)
      else pure acc
    else pure acc
  have hstep (s : Finset (Fin n)) (k : ℕ) (i : Fin n) :
      (step (s,k) i).val =
        if i ∈ A then
          if decide (M.Indep (insert i s : Set (Fin n))) then (insert i s,k+1) else (s,k)
        else (s,k) := by
    by_cases hi : i ∈ A
    · simp [step, CountingMatroid.Model.Operations.containsElement,
        CountingMatroid.Model.Operations.insertElement,
        CountingMatroid.Model.Operations.encodeQuery,
        CountingMatroid.Model.Operations.oracleQuery,
        CountingMatroid.Model.Operations.successor, hi]
      have hquery : (fun j : Fin n => decide (j = i) || decide (j ∈ s)) =
          (fun j => decide (j ∈ insert i s)) := by
        funext j
        simp [Finset.mem_insert]
      rw [hquery, hq]
      simp only [decide_eq_true_eq]
      simp only [Finset.coe_insert]
      split_ifs <;> simp
    · simp [step, CountingMatroid.Model.Operations.containsElement, hi]
  have hfold : ∀ (l : List (Fin n)) (s P : Finset (Fin n)) (k : ℕ),
      l.Nodup → Disjoint P l.toFinset → k = s.card →
      M.IsBasis (s : Set (Fin n)) (P : Set (Fin n)) →
      let out := (Arlib.Computation.Charged.foldl step l (s,k)).val
      M.IsBasis (out.1 : Set (Fin n)) ((P ∪ (A ∩ l.toFinset)) : Set (Fin n)) ∧
        out.2 = out.1.card := by
    intro l
    induction l with
    | nil =>
      intro s P k _ _ hk hb
      simpa [hk] using hb
    | cons i l ih =>
      intro s P k hnodup hdisj hk hb
      rw [Arlib.Computation.Charged.val_foldl_cons, hstep]
      have hnodup' : l.Nodup := hnodup.of_cons
      have hiTail : i ∉ l.toFinset := by simpa using hnodup.notMem
      have hPtail : Disjoint P l.toFinset :=
        hdisj.mono_right (by simp)
      have hiP : i ∉ P := by
        intro hip
        exact (Finset.disjoint_left.mp hdisj hip) (by simp)
      have his : i ∉ s := by
        intro his
        exact hiP (hb.subset his)
      have hPinsertTail : Disjoint (insert i P) l.toFinset :=
        Finset.disjoint_insert_left.mpr ⟨hiTail, hPtail⟩
      by_cases hi : i ∈ A
      · simp only [if_pos hi]
        by_cases hind : M.Indep (insert i s : Set (Fin n))
        · simp only [decide_eq_true_eq, if_pos hind]
          have hb' : M.IsBasis ((insert i s : Finset (Fin n)) : Set (Fin n))
              ((insert i P : Finset (Fin n)) : Set (Fin n)) := by
            simpa using hb.insert_isBasis_insert hind
          have hk' : k + 1 = (insert i s).card := by simp [hk, his]
          have h := ih (insert i s) (insert i P) (k+1)
            hnodup' hPinsertTail hk' hb'
          have hsets : P ∪ (A ∩ (i :: l).toFinset) =
              insert i P ∪ (A ∩ l.toFinset) := by
            ext x
            simp [hi]
          simpa only [← Finset.coe_union, ← Finset.coe_inter, hsets] using h
        · simp only [decide_eq_true_eq, if_neg hind]
          have heClosure : i ∈ M.closure (s : Set (Fin n)) :=
            (hb.indep.mem_closure_iff').2 ⟨by rw [hfull]; trivial, fun h => False.elim (hind h)⟩
          have hb' : M.IsBasis (s : Set (Fin n))
              ((insert i P : Finset (Fin n)) : Set (Fin n)) := by
            apply (M.isBasis_iff_indep_subset_closure).2
            refine ⟨hb.indep, ?_, ?_⟩
            · exact hb.subset.trans (by simp)
            · intro x hx
              rcases (Finset.mem_insert.mp hx) with rfl | hxP
              · exact heClosure
              · exact hb.subset_closure hxP
          have h := ih s (insert i P) k hnodup' hPinsertTail hk hb'
          have hsets : P ∪ (A ∩ (i :: l).toFinset) =
              insert i P ∪ (A ∩ l.toFinset) := by
            ext x
            simp [hi]
          simpa only [← Finset.coe_union, ← Finset.coe_inter, hsets] using h
      · simp only [if_neg hi]
        have h := ih s P k hnodup' hPtail hk hb
        have hsets : P ∪ (A ∩ (i :: l).toFinset) =
            P ∪ (A ∩ l.toFinset) := by
          ext x
          simp [hi]
        simpa only [← Finset.coe_union, ← Finset.coe_inter, hsets] using h
  unfold CountingMatroid.Model.Subroutines.greedyRank
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]
  have hbase := hfold (List.finRange n) ∅ ∅ 0 (List.nodup_finRange n)
    (by simp) (by simp) (by simpa using M.empty_indep.isBasis_self)
  have hB : M.IsBasis
      (((Arlib.Computation.Charged.foldl step (List.finRange n)
        ((∅ : Finset (Fin n)), 0)).val).1 : Set (Fin n))
      (A : Set (Fin n)) := by
    simpa using hbase.1
  rw [hbase.2]
  simpa using hB.encard_eq_eRk
