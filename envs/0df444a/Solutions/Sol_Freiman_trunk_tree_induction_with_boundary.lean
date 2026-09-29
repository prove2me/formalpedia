-- Prove2me | solution 1 for Freiman.trunk_tree_induction_with_boundary
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:42:48.988476+00:00
-- url     : https://prove2.me/submissions/d5175891-4ed2-4043-9ad2-a5d63666e9fe

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman
theorem solution (C : TrunkCatalog) (hw : trunkAllWitnesses C)
    (he : ∀ w : TrunkWitness, trunkWitnessValid C w → TrunkWitnessExclusion C w)
    (hs : ∀ (R : CertRectangle) (axis : Bool), certRectangleValid R → ∀ r s : ℝ, certRectangleMem R r s →
      (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
      (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s))
    (hb : ∀ (R : CertRectangle) (bs : List CertBound), trunkBoundaryBound R bs → ∀ r s q : ℝ, certRectangleMem R r s → ¬ trunkHolds bs r s q) :
    TrunkTreeSound C := by
  have leaf (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ)
      (ht : trunkLeafBound C R bs id sign) (r s q : ℝ)
      (hm : certRectangleMem R r s)
      (hside : sign = 0 ∨ 0 ≤ (sign : ℝ) * (r-s)) :
      ¬ trunkHolds bs r s q := by
    rcases ht with ⟨hid, hsize, hd, hcontains, l, hl, u, hu, huse⟩
    intro hholds
    have hvalid := hw id hid hsize
    have hmem : certRectangleMem (trunkWitness C id).rectangle r s := by
      rcases hcontains with ⟨hlo, hhi, hlo', hhi'⟩
      rcases hm with ⟨hr0, hr1, hs0, hs1⟩
      exact ⟨le_trans (by exact_mod_cast hlo) hr0,
        le_trans hr1 (by exact_mod_cast hhi),
        le_trans (by exact_mod_cast hlo') hs0,
        le_trans hs1 (by exact_mod_cast hhi')⟩
    exact he (trunkWitness C id) hvalid l u huse r s q hmem
      (by simpa only [hd] using hside) ⟨hholds l hl, hholds u hu⟩
  intro R bs tree
  induction tree generalizing R with
  | pair id =>
      intro _ ht r s q hm
      exact leaf R bs id 0 ht r s q hm (Or.inl rfl)
  | split axis left right ihl ihr =>
      intro hR ht r s q hm hholds
      obtain ⟨hvalid, hmem⟩ := hs R axis hR r s hm
      rcases hmem with hleft | hright
      · exact ihl _ hvalid.1 ht.1 r s q hleft hholds
      · exact ihr _ hvalid.2 ht.2 r s q hright hholds
  | diagonal negative positive =>
      intro _ ht r s q hm
      by_cases h : r ≤ s
      · exact leaf R bs negative (-1) ht.1 r s q hm (Or.inr (by norm_num; linarith))
      · exact leaf R bs positive 1 ht.2 r s q hm (Or.inr (by norm_num; linarith))
  | boundary =>
      intro _ ht r s q hm
      exact hb R bs ht r s q hm
