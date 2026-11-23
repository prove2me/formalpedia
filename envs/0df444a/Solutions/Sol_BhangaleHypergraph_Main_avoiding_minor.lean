-- Prove2me | solution 1 for BhangaleHypergraph.Main.avoiding_minor
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:17.003991+00:00
-- url     : https://prove2.me/submissions/65de899a-64e0-4067-9bef-cf985976eadb

import Definitions.Def_BhangaleHypergraph_Main_Restricted

open BhangaleHypergraph.Main

theorem solution {R R' C : ℕ} (hR : 1 ≤ R) (hR' : 1 ≤ R') (hC : 2 ≤ C)
    {W : Finset (Finset (Fin R))} {W' : Finset (Finset (Fin R'))}
    (hW : TestDomain W) (hW' : TestDomain W') (f : W → Fin C) (g : W' → Fin C)
    (π : Fin R → Fin R') (hminor : ExactMinor f g π)
    (S : Finset (Fin R)) (T : Finset (Fin C)) (hS : Avoids f S T) :
    Avoids g (S.image π) T := by
  intro Y hSY
  obtain ⟨hpre, hcolor⟩ := hminor Y
  rw [hcolor]
  apply hS ⟨Preimage π Y.val, hpre⟩
  intro x hx
  simp only [Preimage, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hSY (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
