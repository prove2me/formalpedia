-- Prove2me | solution 1 for Erdos77.spencer_1975_uniform_edge_coloring_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T17:46:56.276593+00:00
-- url     : https://prove2.me/submissions/14d94971-ee48-4c8f-8854-67f905dcb27c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Erdos77_spencer_1975_unordered_edge_coloring_lll_core

theorem solution (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun (c : Fin n -> Fin n -> Bool) =>
      And (forall a b : Fin n, a != b -> c a b = c b a)
        (forall s : Finset (Fin n), s.card = k ->
          And (Exists fun (a : Fin n) => Exists fun (b : Fin n) => And (Membership.mem s a) (And (Membership.mem s b) (And (a != b) (c a b = true))))
            (Exists fun (a : Fin n) => Exists fun (b : Fin n) => And (Membership.mem s a) (And (Membership.mem s b) (And (a != b) (c a b = false))))) := by
  classical
  obtain ⟨edgeColor, hedge⟩ :=
    Erdos77.spencer_1975_unordered_edge_coloring_lll_core (Fin n) k hk
      (by simpa using hkn) (by simpa using hcond)
  let c : Fin n -> Fin n -> Bool := fun a b =>
    if hab : a = b then false
    else edgeColor ⟨{a, b}, Finset.card_pair hab⟩
  refine ⟨c, ?_, ?_⟩
  · intro a b hab
    have hab' : a ≠ b := by simpa using hab
    simp [c, hab', Ne.symm hab', Finset.pair_comm]
  · intro s hs
    constructor
    · rcases (hedge s hs).1 with ⟨e, hes, hetrue⟩
      rcases Finset.card_eq_two.mp e.property with ⟨a, b, hab, he⟩
      have heq : e = ⟨{a, b}, Finset.card_pair hab⟩ := Subtype.ext he
      refine ⟨a, b, hes a (by rw [he]; simp), hes b (by rw [he]; simp), ?_, ?_⟩
      · simpa using hab
      simpa [c, hab, heq] using hetrue
    · rcases (hedge s hs).2 with ⟨e, hes, hefalse⟩
      rcases Finset.card_eq_two.mp e.property with ⟨a, b, hab, he⟩
      have heq : e = ⟨{a, b}, Finset.card_pair hab⟩ := Subtype.ext he
      refine ⟨a, b, hes a (by rw [he]; simp), hes b (by rw [he]; simp), ?_, ?_⟩
      · simpa using hab
      simpa [c, hab, heq] using hefalse
