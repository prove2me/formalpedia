-- Prove2me | solution 1 for Freiman.section14_record_from_pair
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:19:38.995057+00:00
-- url     : https://prove2.me/submissions/08d1dca5-3f15-45fa-b277-4f486ae4b2d4

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic

open Freiman

private theorem rect_mono {outer inner : CertRectangle} {r s : ℝ}
    (hc : section14RectangleContains outer inner) (h : certRectangleMem inner r s) :
    certRectangleMem outer r s := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨le_trans ?_ h1, le_trans h2 ?_, le_trans ?_ h3, le_trans h4 ?_⟩
  · exact_mod_cast c1
  · exact_mod_cast c2
  · exact_mod_cast c3
  · exact_mod_cast c4

theorem solution (hw : ∀ w : CertWitness, certWitnessValid w → ∀ r s q : ℝ,
      certRectangleMem w.rectangle r s →
      ¬ (certBoundHolds w.lowerBound r s q ∧ certBoundHolds w.upperBound r s q)) :
    ∀ (C : Section14Catalog) (si : ℕ) (rec : Section14Record),
      section14RecordValid C si rec → section14RecordSound C si rec := by
  intro C si rec hvalid
  unfold section14RecordValid at hvalid
  obtain ⟨-, -, -, -, -, hcond, a, ha, -, -, -, -, hft, hst, hcontain, hvw⟩ := hvalid
  intro par hpar hbranch r s q hrect hholds
  obtain ⟨hlo, hup⟩ := hcond par hpar hbranch
  refine hw _ hvw r s q (rect_mono hcontain hrect) ?_
  exact ⟨hholds _ hlo, hholds _ hup⟩
