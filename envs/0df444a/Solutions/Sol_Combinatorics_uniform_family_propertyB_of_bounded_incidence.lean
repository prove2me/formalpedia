-- Prove2me | solution 1 for Combinatorics.uniform_family_propertyB_of_bounded_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:01:55.571991+00:00
-- url     : https://prove2.me/submissions/c169d50a-ae4d-4456-b640-3ff64417eeb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Combinatorics_finite_symmetric_local_lemma
import Theorems.Thm_Combinatorics_uniform_family_monochromatic_event_data

theorem solution
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m)
    (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D)
    (hcond : (4 : Real) * (m : Real) * (D : Real) * (2 : Real) ^ (1 - (m : Real)) < 1) :
    Exists fun c : X -> Bool => forall i,
      (Exists fun x => Membership.mem (B i) x /\ c x = true) /\
      (Exists fun x => Membership.mem (B i) x /\ c x = false) := by
  classical
  by_cases hI : Nonempty I
  · let i0 : I := Classical.choice hI
    have hD : 0 < D := by
      have hcard : 0 < (B i0).card := by rw [hsize]; exact hm
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
      have hi : Membership.mem (Finset.univ.filter (fun i => Membership.mem (B i) x)) i0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
      have hpos : 0 < (Finset.univ.filter (fun i => Membership.mem (B i) x)).card :=
        Finset.card_pos.mpr ⟨i0, hi⟩
      have hbound := hdegree x
      omega
    let A : I -> Finset (X -> Bool) := fun i =>
      Finset.univ.filter (fun c =>
        (forall x, Membership.mem (B i) x -> c x = true) \/
        (forall x, Membership.mem (B i) x -> c x = false))
    let dep : I -> I -> Prop := fun i j =>
      i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
    obtain ⟨hneighbors, hprob, hindependent⟩ :=
      Combinatorics.uniform_family_monochromatic_event_data X I B m D hm hsize hdegree
    let d : Nat := m * D - 1
    let p : Real := (2 : Real) ^ (1 - (m : Real))
    have hdplus : d + 1 = m * D := by
      change (m * D - 1) + 1 = m * D
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.mul_pos hm hD))
    have hcondLLL : 4 * p * ((d + 1 : Nat) : Real) < 1 := by
      calc
        4 * p * ((d + 1 : Nat) : Real) =
            4 * (m : Real) * (D : Real) * (2 : Real) ^ (1 - (m : Real)) := by
          dsimp [p]
          rw [hdplus]
          push_cast
          ring
        _ < 1 := hcond
    obtain ⟨w, hw⟩ :=
      Combinatorics.finite_symmetric_local_lemma (X -> Bool) I A dep d p
        hneighbors hprob hindependent hcondLLL
    refine ⟨w, ?_⟩
    intro i
    constructor
    · by_contra hred
      have hallFalse : forall x, Membership.mem (B i) x -> w x = false := by
        intro x hx
        cases hc : w x
        · rfl
        · exact False.elim (hred ⟨x, ⟨hx, hc⟩⟩)
      have hevent : Membership.mem (A i) w := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Or.inr hallFalse⟩
      exact hw i hevent
    · by_contra hblue
      have hallTrue : forall x, Membership.mem (B i) x -> w x = true := by
        intro x hx
        cases hc : w x
        · exact False.elim (hblue ⟨x, ⟨hx, hc⟩⟩)
        · rfl
      have hevent : Membership.mem (A i) w := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Or.inl hallTrue⟩
      exact hw i hevent
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    refine ⟨fun _ => true, ?_⟩
    intro i
    exact isEmptyElim i
