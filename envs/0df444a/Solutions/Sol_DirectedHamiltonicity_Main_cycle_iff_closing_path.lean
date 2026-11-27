-- Prove2me | solution 1 for DirectedHamiltonicity.Main.cycle_iff_closing_path
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:42:43.292082+00:00
-- url     : https://prove2.me/submissions/75dce044-7b87-41a6-b0b1-8534432cdd36

import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms
import Mathlib

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph Classical

/-- Delete loops, arcs into the start, and arcs out of the end. -/
def pathAdj {n : ℕ} (adj : Fin n → Fin n → Bool) (s t u v : Fin n) : Prop :=
  adj u v = true ∧ u ≠ v ∧ v ≠ s ∧ u ≠ t

instance {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) : DecidableRel (pathAdj adj s t) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private def rawPath {n : ℕ} (a : Fin n → Fin n → Prop) (s t : Fin n) (k : ℕ) : Prop :=
  ∃ P : Fin k → {e : Fin n × Fin n // a e.1 e.2},
    (∀ i, (ofAdj a).tail (P i) = (ofAdj a).walkVerts s P i.castSucc) ∧
    Function.Injective ((ofAdj a).walkVerts s P) ∧ (ofAdj a).walkVerts s P (Fin.last k) = t

theorem order_path_iff {k : ℕ} (a : Fin (k+1) → Fin (k+1) → Prop) [DecidableRel a]
    (s t : Fin (k+1)) :
    ((ofAdj a).hamPaths s t).Nonempty ↔
      ∃ σ : Equiv.Perm (Fin (k+1)), σ 0 = s ∧ σ (Fin.last k) = t ∧
        ∀ i : Fin k, a (σ i.castSucc) (σ i.succ) := by
  classical
  unfold hamPaths IsHamPath
  simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
  change rawPath a s t (Fintype.card (Fin (k+1))-1) ↔ _
  rw [show Fintype.card (Fin (k+1))-1 = k by simp]
  unfold rawPath
  constructor
  · rintro ⟨P, ht, inj, last⟩
    let σ := Equiv.ofBijective ((ofAdj a).walkVerts s P)
      (Finite.injective_iff_bijective.mp inj)
    refine ⟨σ, rfl, last, fun i => ?_⟩
    change a ((ofAdj a).walkVerts s P i.castSucc) ((P i).val.2)
    rw [← ht i]
    exact (P i).property
  · rintro ⟨σ, first, last, arcs⟩
    let P (i : Fin k) : {p : Fin (k+1) × Fin (k+1) // a p.1 p.2} := ⟨(σ i.castSucc, σ i.succ),arcs i⟩
    have walk : (ofAdj a).walkVerts s P = σ := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact first.symm
      · rfl
    refine ⟨P, ?_, ?_, ?_⟩
    · intro i
      rw [walk]
      rfl
    · exact walk ▸ σ.injective
    · rw [walk]; exact last

/-- On at least two vertices, cutting and closing an arc is equivalent to the existence of a cycle. -/
theorem cycle_iff_closing_path {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) :
    HasHamCycle n adj ↔ ∃ s t : Fin n, s ≠ t ∧ adj t s = true ∧
      ((ofAdj (pathAdj adj s t)).hamPaths s t).Nonempty := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  let l := k+1
  constructor
  · rintro ⟨_, σ, arcs⟩
    let s := σ 0
    let t := σ (Fin.last l)
    have ends : s ≠ t := fun e => by
      have q := congrArg Fin.val (σ.injective e)
      change 0 = k+1 at q
      omega
    refine ⟨s,t,ends,?_,(order_path_iff _ _ _).2 ⟨σ,rfl,rfl,?_⟩⟩
    · simpa [s,t,l,finRotate_last] using arcs (Fin.last l)
    · intro i
      have rot : finRotate (l+1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      refine ⟨rot ▸ arcs i.castSucc, fun e => ?_, fun e => ?_, fun e => ?_⟩
      · have q := congrArg Fin.val (σ.injective e)
        change i.val = i.val+1 at q
        omega
      · exact Fin.succ_ne_zero i (σ.injective e)
      · exact Fin.castSucc_ne_last i (σ.injective e)
  · rintro ⟨s,t,_,close,hp⟩
    obtain ⟨σ,first,last,arcs⟩ := (order_path_iff _ _ _).1 hp
    refine ⟨by omega, σ, fun j => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [finRotate_last,first,last] using close
    · rw [show finRotate (k+1+1) i.castSucc = i.succ from finRotate_of_lt i.isLt]
      exact (arcs i).1

theorem smallCycleAnswer_correct {n : ℕ} (hn : n ≤ 1) (adj : Fin n → Fin n → Bool) :
    smallCycleAnswer n adj = true ↔ HasHamCycle n adj := by
  interval_cases n
  · simp [smallCycleAnswer,HasHamCycle]
  · change adj 0 0 = true ↔ _
    simp only [HasHamCycle, Nat.zero_lt_succ, true_and]
    constructor
    · intro h
      refine ⟨Equiv.refl _, fun i => ?_⟩
      simpa only [Subsingleton.elim i (0 : Fin 1),finRotate_one,Equiv.refl_apply] using h
    · rintro ⟨σ,h⟩
      simpa only [finRotate_one,Equiv.refl_apply,Subsingleton.elim (σ 0) (0 : Fin 1)] using h 0

end DirectedHamiltonicity.Main.CycleReduction

open DirectedHamiltonicity.Main

open Classical in
theorem solution {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) :
    HasHamCycle n adj ↔ ∃ s t : Fin n, s ≠ t ∧ adj t s = true ∧
      ((ofAdj (fun u v => adj u v = true ∧ u ≠ v ∧ v ≠ s ∧ u ≠ t)).hamPaths s t).Nonempty := by
  exact CycleReduction.cycle_iff_closing_path hn adj
