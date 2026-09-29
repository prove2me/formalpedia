-- Prove2me | solution 1 for Freiman.lower_bridge_interval_chain_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:50:30.152363+00:00
-- url     : https://prove2.me/submissions/6be62ef2-9fec-4ddf-9dd1-c0e0acf5a17b

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

-- A chain of intervals with pairwise-overlapping consecutive members and nonempty
-- members covers its whole span: if some member starts at or below `t` and some member
-- ends at or above `t`, then `t` lies in some member. The proof is structural induction
-- on the list. In the step, if `t` is not in the head's cover then it is strictly below
-- the head's left end or strictly above its right end; the overlap of the head with the
-- next member then either puts the next member's right end at or above `t` (so it can
-- serve as the upper witness) or its left end at or below `t` (so it can serve as the
-- lower witness), and the induction hypothesis applies to the tail.
private lemma chain_cover (base : LowerPair) :
    ∀ (ls : List LowerPair),
      (∀ d ∈ ls, lowerEndpoint (lowerPhysicalAdd base d) false ≤
        lowerEndpoint (lowerPhysicalAdd base d) true) →
      ls.IsChain (fun a b => (lowerCover (lowerPhysicalAdd base a) ∩
        lowerCover (lowerPhysicalAdd base b)).Nonempty) →
      ∀ t : ℝ, (∃ a ∈ ls, ∃ b ∈ ls,
        lowerEndpoint (lowerPhysicalAdd base a) false ≤ t ∧
        t ≤ lowerEndpoint (lowerPhysicalAdd base b) true) →
      ∃ d ∈ ls, t ∈ lowerCover (lowerPhysicalAdd base d)
  | [], _, _, t, ht => by
      obtain ⟨a, ha, _⟩ := ht
      exact absurd ha List.not_mem_nil
  | a0 :: rest, hv, hc, t, ht => by
      by_cases hmid : lowerEndpoint (lowerPhysicalAdd base a0) false ≤ t ∧
          t ≤ lowerEndpoint (lowerPhysicalAdd base a0) true
      · exact ⟨a0, List.mem_cons_self .., hmid⟩
      · have hle : lowerEndpoint (lowerPhysicalAdd base a0) false ≤
            lowerEndpoint (lowerPhysicalAdd base a0) true :=
          hv a0 (List.mem_cons_self ..)
        have hcase : t < lowerEndpoint (lowerPhysicalAdd base a0) false ∨
            lowerEndpoint (lowerPhysicalAdd base a0) true < t := by
          rcases lt_or_ge t (lowerEndpoint (lowerPhysicalAdd base a0) false) with h | h
          · exact Or.inl h
          · exact Or.inr (by
              by_contra hcon
              exact hmid ⟨h, le_of_not_gt hcon⟩)
        cases rest with
        | nil =>
            obtain ⟨a, ha, b, hb, hlo, hhi⟩ := ht
            simp only [List.mem_singleton] at ha hb
            subst ha
            subst hb
            exact absurd ⟨hlo, hhi⟩ hmid
        | cons b l' =>
            have hRb : (lowerCover (lowerPhysicalAdd base a0) ∩
                lowerCover (lowerPhysicalAdd base b)).Nonempty := by
              have h := hc
              rw [List.isChain_cons_iff _ a0 (b :: l')] at h
              rcases h with hnil | ⟨b', l'', hR, _, heq⟩
              · exact absurd hnil (by simp)
              · obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp heq
                exact hR
            obtain ⟨s, hs⟩ := hRb
            rw [Set.mem_inter_iff] at hs
            obtain ⟨hs0, hsb⟩ := hs
            rw [lowerCover, Set.mem_Icc] at hs0 hsb
            rcases hcase with hlt | hgt
            · -- t is below the head's left end; the tail's head brackets it above
              obtain ⟨u, hu, _b2, _hb2, hlo_u, _hhi2⟩ := ht
              have hu_rest : u ∈ b :: l' := by
                rcases List.mem_cons.mp hu with rfl | h
                · exact absurd hlo_u (not_le.mpr hlt)
                · exact h
              have hb_hi : t ≤ lowerEndpoint (lowerPhysicalAdd base b) true := by
                linarith [hlt, hs0.1, hsb.2]
              obtain ⟨d', hd', hcov'⟩ := chain_cover base (b :: l')
                (fun x hx => hv x (List.mem_cons_of_mem a0 hx)) hc.tail t
                ⟨u, hu_rest, b, List.mem_cons_self .., hlo_u, hb_hi⟩
              exact ⟨d', List.mem_cons_of_mem a0 hd', hcov'⟩
            · -- t is above the head's right end; the tail's head brackets it below
              obtain ⟨_a2, _ha2, w, hw, _hlo2, hhi_w⟩ := ht
              have hw_rest : w ∈ b :: l' := by
                rcases List.mem_cons.mp hw with rfl | h
                · exact absurd hhi_w (not_le.mpr hgt)
                · exact h
              have hb_lo : lowerEndpoint (lowerPhysicalAdd base b) false ≤ t := by
                linarith [hgt, hs0.2, hsb.1]
              obtain ⟨d', hd', hcov'⟩ := chain_cover base (b :: l')
                (fun x hx => hv x (List.mem_cons_of_mem a0 hx)) hc.tail t
                ⟨b, List.mem_cons_self .., w, hw_rest, hb_lo, hhi_w⟩
              exact ⟨d', List.mem_cons_of_mem a0 hd', hcov'⟩

theorem solution (base : LowerPair) (ls : List LowerPair)
    (hv : ∀ d ∈ ls, lowerEndpoint (lowerPhysicalAdd base d) false ≤
      lowerEndpoint (lowerPhysicalAdd base d) true)
    (hc : ls.IsChain (fun a b => (lowerCover (lowerPhysicalAdd base a) ∩
      lowerCover (lowerPhysicalAdd base b)).Nonempty))
    (t : ℝ)
    (ht : ∃ a ∈ ls, ∃ b ∈ ls,
      lowerEndpoint (lowerPhysicalAdd base a) false ≤ t ∧
      t ≤ lowerEndpoint (lowerPhysicalAdd base b) true) :
    ∃ d ∈ ls, t ∈ lowerCover (lowerPhysicalAdd base d) :=
  chain_cover base ls hv hc t ht
