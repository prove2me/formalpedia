-- Prove2me | solution 2 for Erdos77.spencer_1975_lll_bad_graph_criterion_fin_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T14:28:26.288478+00:00
-- url     : https://prove2.me/submissions/5c59c882-6263-4df2-8ffd-3d7d0e0a16e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Erdos77_spencer_1975_uniform_edge_coloring_core

theorem solution (k n : Nat) (hk : 2 <= k) (hkn : k <= n)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) * (Nat.choose (n - 2) (k - 2) : Real) *
        (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph (Fin n) =>
      And (Not (Exists fun s : Finset (Fin n) => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset (Fin n) =>
          And (s.card = k) ((Compl.compl G).IsClique s))) := by
  obtain ⟨c, hsymm, hcolor⟩ :=
    Erdos77.spencer_1975_uniform_edge_coloring_core k n hk hkn hcond
  let G : SimpleGraph (Fin n) := {
    Adj := fun a b => (a = b -> False) ∧ c a b = true
    symm := ⟨by
      intro a b h
      rcases h with ⟨hne, hc⟩
      refine ⟨fun heq => hne heq.symm, ?_⟩
      have hs := hsymm a b (by simpa using hne)
      simpa [hs] using hc⟩
    loopless := ⟨by
      intro a h
      exact h.1 rfl⟩
  }
  refine ⟨G, ?_, ?_⟩
  · rintro ⟨s, hs, hcl⟩
    rcases (hcolor s hs).2 with ⟨a, b, ha, hb, hab, hfalse⟩
    have hne : a = b -> False := by simpa using hab
    have hadj := hcl ha hb hne
    dsimp [G] at hadj
    rw [hfalse] at hadj
    cases hadj.2
  · rintro ⟨s, hs, hcl⟩
    rcases (hcolor s hs).1 with ⟨a, b, ha, hb, hab, htrue⟩
    have hne : a = b -> False := by simpa using hab
    have hnot : ¬ (Compl.compl G).Adj a b := by
      intro hcomp
      rcases (SimpleGraph.compl_adj G a b).1 hcomp with ⟨_, hnotG⟩
      apply hnotG
      dsimp [G]
      exact ⟨hne, htrue⟩
    exact hnot (hcl ha hb hne)