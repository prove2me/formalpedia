-- Prove2me | solution 1 for Erdos77.spencer_1975_uniform_hyperedge_coloring_lll_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T18:45:34.738976+00:00
-- url     : https://prove2.me/submissions/95b2680d-b168-4786-9297-d1222e53eb1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Combinatorics_uniform_family_propertyB_of_bounded_incidence

theorem solution (V : Type*) [Fintype V]
    [DecidableEq V] (r k : Nat) (hr : 1 <= r) (hrk : r <= k)
    (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k r : Real) *
          (Nat.choose (Fintype.card V - r) (k - r) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k r : Real)) < 1) :
    Exists fun c : {e : Finset V // e.card = r} -> Bool =>
      forall s : Finset V, s.card = k ->
        And
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = true))
          (Exists fun e : {e : Finset V // e.card = r} =>
            And (forall v : V, Membership.mem (e : Finset V) v -> Membership.mem s v) (c e = false)) := by
  classical
  let E := {e : Finset V // e.card = r}
  let K := {s : Finset V // s.card = k}
  let B : K → Finset E := fun s => Finset.univ.filter (fun e => e.val ⊆ s.val)
  have hsize : ∀ s, (B s).card = Nat.choose k r := by
    intro s
    calc
      (B s).card = (s.val.powersetCard r).card := by
        apply Finset.card_bij (fun e _ => e.val)
        · intro e he
          exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp he).2, e.property⟩
        · intro e he f hf h
          exact Subtype.ext h
        · intro e he
          have h := Finset.mem_powersetCard.mp he
          exact ⟨⟨e, h.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, rfl⟩
      _ = Nat.choose k r := by rw [Finset.card_powersetCard, s.property]
  have hdegree : ∀ e : E,
      (Finset.univ.filter (fun s => e ∈ B s)).card ≤
        Nat.choose (Fintype.card V - r) (k - r) := by
    intro e
    have hcount :
        (Finset.univ.filter (fun s => e ∈ B s)).card =
          (((Finset.univ : Finset V).powersetCard k).filter (e.val ⊆ ·)).card := by
      apply Finset.card_bij (fun s _ => s.val)
      · intro s hs
        have hes : e.val ⊆ s.val := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).2).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.property⟩, hes⟩
      · intro s hs t ht h
        exact Subtype.ext h
      · intro s hs
        have hsk := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
        have hes := (Finset.mem_filter.mp hs).2
        refine ⟨⟨s, hsk⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hes⟩⟩
    rw [hcount, Finset.card_filter_powersetCard_subset _ _ _
      (Finset.subset_univ _) (by simpa only [e.property] using hrk)]
    simp only [Finset.card_univ, e.property, le_refl]
  obtain ⟨c, hc⟩ := Combinatorics.uniform_family_propertyB_of_bounded_incidence
    E K B (Nat.choose k r) (Nat.choose (Fintype.card V - r) (k - r))
    (Nat.choose_pos hrk) hsize hdegree hcond
  refine ⟨c, ?_⟩
  intro s hs
  rcases hc ⟨s, hs⟩ with ⟨⟨e, he, htrue⟩, ⟨f, hf, hfalse⟩⟩
  exact ⟨⟨e, (Finset.mem_filter.mp he).2, htrue⟩,
    ⟨f, (Finset.mem_filter.mp hf).2, hfalse⟩⟩
