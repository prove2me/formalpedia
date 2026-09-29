-- Prove2me | solution 1 for Combinatorics.uniform_family_monochromatic_event_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:33:23.333368+00:00
-- url     : https://prove2.me/submissions/997deb81-96f6-411e-afc7-e2fb2c626923

import Mathlib
set_option autoImplicit false

theorem solution
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D) :
    (let dep : I -> I -> Prop := fun i j =>
      i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
     (forall i, (Finset.univ.filter (fun j => dep i j)).card <= m * D - 1)) := by
  change forall k : I, (Finset.univ.filter (fun j : I =>
    k != j /\ Exists fun x : X => Membership.mem (B k) x /\ Membership.mem (B j) x)).card <= m * D - 1
  intro k
  classical
  let inc : X -> Finset I := fun x => Finset.univ.filter (fun j => Membership.mem (B j) x)
  let part : X -> Finset I := fun x => (inc x).erase k
  have hinc (x : X) : (inc x).card <= D := by
    simpa [inc] using hdegree x
  have hpart (x : X) (hx : Membership.mem (B k) x) : (part x).card <= D - 1 := by
    have hi : Membership.mem (inc x) k := by simp [inc, hx]
    change ((inc x).erase k).card <= D - 1
    rw [Finset.card_erase_of_mem hi]
    have := hinc x
    omega
  let neigh : Finset I := Finset.univ.filter (fun j =>
    k != j /\ Exists fun x : X => Membership.mem (B k) x /\ Membership.mem (B j) x)
  have hcard : neigh.card <= Finset.sum (B k) (fun x => (part x).card) := by
    calc
      neigh.card <= ((B k).biUnion part).card := by
        apply Finset.card_le_card
        intro j hj
        have hj' := (Finset.mem_filter.mp hj).2
        cases hj'.2 with
        | intro x hx =>
          cases hx with
          | intro hxk hxj =>
            apply Finset.mem_biUnion.mpr
            apply Exists.intro x
            apply And.intro hxk
            change Membership.mem (part x) j
            simp [part, Finset.mem_erase, inc, hxj]; exact Ne.symm (by simpa using hj'.1)
      _ <= Finset.sum (B k) (fun x => (part x).card) := Finset.card_biUnion_le
  have hsum : Finset.sum (B k) (fun x => (part x).card) <= (B k).card * (D - 1) := by
    calc
      Finset.sum (B k) (fun x => (part x).card) <= Finset.sum (B k) (fun _ => D - 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpart x hx
      _ = (B k).card * (D - 1) := by simp
  have hmD : (B k).card * (D - 1) <= m * D - 1 := by
    rw [hsize k]
    have hDpos : 0 < D := by
      have hcardpos : 0 < (B k).card := by rw [hsize k]; omega
      have hmem := Finset.card_pos.mp hcardpos
      cases hmem with
      | intro x hx =>
        have hxi : Membership.mem (B k) x := hx
        have hxD := hdegree x
        have hin : Membership.mem (Finset.univ.filter (fun i : I => Membership.mem (B i) x)) k := by simp [hxi]
        have hpos : 0 < (Finset.univ.filter (fun i : I => Membership.mem (B i) x)).card :=
          Finset.card_pos.mpr (Exists.intro k hin)
        omega
    rw [Nat.mul_sub_left_distrib]
    omega
  change neigh.card <= m * D - 1
  exact hcard.trans (hsum.trans hmD)
