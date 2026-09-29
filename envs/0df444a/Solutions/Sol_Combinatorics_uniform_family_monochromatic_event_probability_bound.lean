-- Prove2me | solution 1 for Combinatorics.uniform_family_monochromatic_event_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:30:31.251347+00:00
-- url     : https://prove2.me/submissions/56690c31-71d1-4125-bf70-44d0b40593dd

import Theorems.Thm_Combinatorics_single_set_monochromatic_event_probability_bound

theorem solution
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D) :
    (let A : I -> Finset (X -> Bool) := fun i =>
      Finset.univ.filter (fun c =>
        (forall x, Membership.mem (B i) x -> c x = true) \/
        (forall x, Membership.mem (B i) x -> c x = false))
     (forall i, ((A i).card : Real) / (Fintype.card (X -> Bool) : Real) <=
      (2 : Real) ^ (1 - (m : Real)))) := by
  dsimp
  intro i
  exact Combinatorics.single_set_monochromatic_event_probability_bound
    X (B i) m hm (hsize i)
