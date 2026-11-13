-- Prove2me | solution 1 for DirKECC1549.Main.trail_family_flow
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:45:48.257147+00:00
-- url     : https://prove2.me/submissions/459158ee-e5ff-49a1-a8b8-037d122ceb51

import Theorems.Thm_DirKECC1549_Main_unit_flow_add_trail
set_option autoImplicit false
open DirKECC1549.Main

private theorem family_flow {n m : ℕ} {α : Type} [DecidableEq α]
    (D : Fin m → Fin n × Fin n) (u v : Fin n)
    (P : α → List (Fin m)) (I : Finset α)
    (hP : ∀ i ∈ I, IsTrail D u (P i) v)
    (hd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i).toFinset (P j).toFinset) :
    IsUnitFlow D (I.biUnion (fun i ↦ (P i).toFinset)) u v I.card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [IsUnitFlow]
  | @insert a I ha ih =>
    have hrest : ∀ i ∈ I, IsTrail D u (P i) v := by
      intro i hi
      exact hP i (by simp [hi])
    have hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (P i).toFinset (P j).toFinset := by
      intro i hi j hj hij
      exact hd i (by simp [hi]) j (by simp [hj]) hij
    have hflow := ih hrest hdis
    have hdisjoint : Disjoint (I.biUnion (fun i ↦ (P i).toFinset)) (P a).toFinset := by
      apply Finset.disjoint_left.mpr
      intro e he hea
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
      have hia : i ≠ a := by intro h; subst i; contradiction
      exact Finset.disjoint_left.mp (hd i (by simp [hi]) a (by simp) hia) hei hea
    have hh := unit_flow_add_trail D u v I.card _ (P a) hflow (hP a (by simp)) hdisjoint
    simpa [Finset.biUnion_insert, ha, Finset.union_comm] using hh

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (q : ℕ) (P : Fin q → List (Fin m))
    (hP : ∀ i, IsTrail D u (P i) v)
    (hd : ∀ i j, i ≠ j → Disjoint (P i).toFinset (P j).toFinset) :
    IsUnitFlow D (Finset.univ.biUnion (fun i ↦ (P i).toFinset)) u v q := by
  simpa using family_flow D u v P Finset.univ (by simpa using hP) (by simpa using hd)
