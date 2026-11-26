-- Prove2me | solution 1 for C6BipartiteDomination.singleton_privateExternalNeighbors_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:58.956799+00:00
-- url     : https://prove2.me/submissions/76a2d437-ef59-4355-bb12-8f4d9fc5beaa

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
import Theorems.Thm_C6BipartiteDomination_mem_internalArcs
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {b p : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b)
    (hP : privateExternalNeighbors G D b = {p}) : False := by
  classical
  let E := insert p (D.erase b)
  have hpP : p ∈ privateExternalNeighbors G D b := by rw [hP]; simp
  have hpInfo := (mem_privateExternalNeighbors G D b p).mp hpP
  have hpNotD : p ∉ D := hpInfo.1
  have hpPriv := hpInfo.2
  have hEd : Dominates G E := by
    intro v hvE
    by_cases hvD : v ∈ D
    · by_cases hvb : v = b
      · subst v
        obtain ⟨u, hu, hAdj⟩ := hb.2
        have hub : u ≠ b := by
          intro heq
          subst u
          exact G.irrefl hAdj
        exact ⟨u, by simp [E, hub, hu], hAdj.symm⟩
      · have hvErase : v ∈ D.erase b := Finset.mem_erase.mpr ⟨hvb, hvD⟩
        exact (hvE (by simpa [E] using Finset.mem_insert_of_mem hvErase)).elim
    · by_cases hret : ∃ d ∈ D.erase b, G.Adj d v
      · rcases hret with ⟨d, hd, hAdj⟩
        exact ⟨d, by simp [E, hd], hAdj⟩
      · obtain ⟨d, hd, hAdj⟩ := hCan.1.1 hvD
        have hdb : d = b := by
          by_contra hne
          exact hret ⟨d, Finset.mem_erase.mpr ⟨hne, hd⟩, hAdj⟩
        subst d
        have hvP : v ∈ privateExternalNeighbors G D b := by
          rw [mem_privateExternalNeighbors]
          refine ⟨hvD, ?_⟩
          intro u hu
          constructor
          · intro huv
            by_cases hub : u = b
            · exact hub
            · exact False.elim (hret ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, huv⟩)
          · intro hub
            rw [hub]
            exact hAdj
        have hvSingle : v ∈ ({p} : Finset V) := by rwa [← hP]
        have hvEq : v = p := Finset.mem_singleton.mp hvSingle
        subst v
        exact (hvE (by simp [E])).elim
  have hEbip : IsBipartiteOn G E := by
    rcases hCan.1.2 with ⟨c, hc⟩
    refine ⟨fun v => if v ∈ D.erase b then c v else false, ?_⟩
    intro u v hu hv hAdj
    change u ∈ insert p (D.erase b) at hu
    change v ∈ insert p (D.erase b) at hv
    rcases Finset.mem_insert.mp hu with huP | huErase
    · subst u
      rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        exact (G.irrefl hAdj).elim
      · have hvD : v ∈ D := Finset.erase_subset b D hvErase
        have hvNe : v ≠ b := (Finset.mem_erase.mp hvErase).1
        have hnot : ¬ G.Adj v p := by
          intro hadj
          exact hvNe ((hpPriv v hvD).mp hadj)
        exact (hnot hAdj.symm).elim
    · rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        have huD : u ∈ D := Finset.erase_subset b D huErase
        have huNe : u ≠ b := (Finset.mem_erase.mp huErase).1
        have hnot : ¬ G.Adj u p := by
          intro hadj
          exact huNe ((hpPriv u huD).mp hadj)
        exact (hnot hAdj).elim
      · simpa only [if_pos huErase, if_pos hvErase] using
          hc (Finset.erase_subset b D huErase) (Finset.erase_subset b D hvErase) hAdj
  have hEbd : IsBipartiteDominatingSet G E := ⟨hEd, hEbip⟩
  have hpNotErase : p ∉ D.erase b := fun hpE => hpNotD (Finset.erase_subset b D hpE)
  have hEcard : E.card = D.card := by
    dsimp [E]
    rw [Finset.card_insert_of_notMem hpNotErase, Finset.card_erase_add_one hb.1]
  have hArcsSub : internalArcs G E ⊆ internalArcs G D := by
    intro q hq
    rcases q with ⟨u, v⟩
    change (u, v) ∈ internalArcs G (insert p (D.erase b)) at hq
    rw [mem_internalArcs] at hq ⊢
    rcases hq with ⟨hu, hv, hAdj⟩
    change u ∈ insert p (D.erase b) at hu
    change v ∈ insert p (D.erase b) at hv
    rcases Finset.mem_insert.mp hu with huP | huErase
    · subst u
      rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        exact (G.irrefl hAdj).elim
      · have hvD : v ∈ D := Finset.erase_subset b D hvErase
        have hvNe : v ≠ b := (Finset.mem_erase.mp hvErase).1
        have hnot : ¬ G.Adj v p := by
          intro hadj
          have heq := (hpPriv v hvD).mp hadj
          exact hvNe heq
        exact (hnot hAdj.symm).elim
    · rcases Finset.mem_insert.mp hv with hvP | hvErase
      · subst v
        have huD : u ∈ D := Finset.erase_subset b D huErase
        have huNe : u ≠ b := (Finset.mem_erase.mp huErase).1
        have hnot : ¬ G.Adj u p := by
          intro hadj
          have heq := (hpPriv u huD).mp hadj
          exact huNe heq
        exact (hnot hAdj).elim
      · exact ⟨Finset.erase_subset b D huErase, Finset.erase_subset b D hvErase, hAdj⟩
  obtain ⟨u, hu, hbu⟩ := hb.2
  have hMissing : (b, u) ∈ internalArcs G D :=
    (mem_internalArcs G D b u).mpr ⟨hb.1, hu, hbu⟩
  have hArcNe : internalArcs G E ≠ internalArcs G D := by
    intro heq
    have hmemE : (b, u) ∈ internalArcs G E := by
      rw [heq]
      exact hMissing
    have hbE : b ∈ E := (mem_internalArcs G E b u).mp hmemE |>.1
    have hbE' : b ∈ insert p (D.erase b) := by simpa [E] using hbE
    rcases Finset.mem_insert.mp hbE' with hbp | hbErase
    · subst p
      exact hpNotD hb.1
    · exact (Finset.mem_erase.mp hbErase).1 rfl
  have hArcLt : (internalArcs G E).card < (internalArcs G D).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hArcsSub, hArcNe⟩)
  have hsecondary := hCan.2.2 E hEbd hEcard
  omega
end C6BipartiteDomination
