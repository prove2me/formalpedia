-- Prove2me | solution 1 for Freiman.trunk_state_from_tree
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:58:22.249526+00:00
-- url     : https://prove2.me/submissions/0afae475-440c-4735-b9b5-abb371ee5383

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

lemma compl_of_not (b : CertBound) (r s q : ℝ) (h : ¬ certBoundHolds b r s q) :
    certBoundHolds (lowerHistoryComplement b) r s q := by
  obtain ⟨lo, st, t⟩ := b
  cases lo <;> cases st <;> simp [certBoundHolds, lowerHistoryComplement] at h ⊢ <;> linarith

theorem solution (C : TrunkCatalog) (k : Fin 16)
    (hb : (∀ g ∈ (C.states k).groups, trunkGroupValid C k g) ∧ trunkCoverage C k)
    (ht : TrunkTreeSound C) :
    trunkStateSound C k := by
  intro pi par hpi hpar r s q hmem hbase goal hg0 hgl bi hbi hb1
  obtain ⟨hgv, hcov⟩ := hb
  obtain ⟨hrv, -, hcov⟩ := hcov
  have hrec : ∀ (goal' : ℕ) (br : ℤ), trunkRecorded C k pi par goal' br →
      ¬ trunkHolds (trunkResidual (C.states k) pi par goal' br) r s q := by
    intro goal' br hr
    obtain ⟨g, hg, hplan, hparent, hgoal, tree, htree⟩ := hr
    have hv := hgv g hg
    obtain ⟨-, -, -, hbt⟩ := hv
    have hbound := (hbt (br, tree) htree).2.2 par hparent
    rw [hplan, hgoal] at hbound
    exact ht _ _ _ hrv hbound r s q hmem
  rcases hcov pi hpi par hpar with h0 | hall
  · exfalso
    apply hrec 0 (-1) h0
    intro b hb
    apply hbase
    simp [trunkResidual, trunkBranch, trunkGoalBranches] at hb
    exact hb
  · rcases hall goal hg0 hgl bi hbi with hauto | hrecd
    · rw [hauto]
      trivial
    · have hne := hrec goal bi hrecd
      unfold trunkResidual at hne
      rcases hb2 : (trunkBranch (C.states k) pi goal bi).2 with _ | _ | a
      · trivial
      · exfalso
        apply hne
        intro x hx
        simp only [hb2, List.append_nil, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hbase x hx
        · exact hb1 x hx
      · show certBoundHolds a r s q
        by_contra hna
        apply hne
        intro x hx
        simp only [hb2, List.mem_append, List.mem_singleton] at hx
        rcases hx with (hx | hx) | rfl
        · exact hbase x hx
        · exact hb1 x hx
        · exact compl_of_not a r s q hna
