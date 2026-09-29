-- Prove2me | solution 1 for Freiman.lower_h5_finite_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:19:07.702985+00:00
-- url     : https://prove2.me/submissions/2edcacaf-8ae3-4a4a-ae07-945a44db91d6

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
set_option Elab.async false
set_option maxHeartbeats 400000
private theorem h5Complement (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  cases hl : b.lower <;> cases hs : b.strict <;>
    simp [certBoundHolds, lowerHistoryComplement, hl, hs]

private theorem h5Residual (c : LowerH5Case) (bi : ℕ) (cs : List CertBound)
    (g : LowerHistoryComparison) (r s q : ℝ)
    (hg : (lowerH5Comparisons c)[bi]? = some (cs,g))
    (hp : lowerHistoryConditions (lowerH5Premises c) r s q)
    (hs : lowerHistoryConditions cs r s q)
    (hn : ¬ lowerHistoryComparisonHolds g r s q) :
    lowerHistoryConditions (lowerH5Residual c bi) r s q := by
  intro b hb
  have hm := hb
  simp only [lowerH5Residual, hg, Option.getD_some, List.mem_eraseDups] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact hp b hm
    · exact hs b hm
  · cases g with
    | automatic => simp at hm
    | impossible => simp at hm
    | bound z =>
      have he : b = lowerHistoryComplement z := List.mem_singleton.mp hm
      subst b
      exact (h5Complement z r s q).2 hn

theorem solution (hex : ∀ (c : LowerH5Case) (record : LowerH5Record), LowerH5RecordBinding c record →
      certWitnessValid (lowerH5Witness record.witness) → ∀ r s q : ℝ,
      certRectangleMem c.rectangle r s → lowerHistoryConditions (lowerH5RecordBounds record) r s q → False) (hb : lowerH5AllBindings) (hw : lowerH5AllWitnesses) :
    ∀ c ∈ lowerH5Cases, lowerH5Numeric c := by
  intro c hc r s q hr hp bi cs g hg hs
  by_cases ha : g = .automatic
  · subst g
    exact Or.inl True.intro
  · rcases (hb c hc).2.2.1 bi cs g hg ha with hrecord | hexception
    · obtain ⟨record, hm, he⟩ := hrecord
      by_cases hgtrue : lowerHistoryComparisonHolds g r s q
      · exact Or.inl hgtrue
      · exfalso
        have hbind := (hb c hc).2.1 record hm
        apply hex c record hbind (hw record.witness hbind.witnessRange.1 hbind.witnessRange.2) r s q hr
        intro b hbrec
        have hmem : b ∈ (lowerH5RecordBounds record).toFinset := List.mem_toFinset.mpr hbrec
        rw [hbind.premise, he] at hmem
        exact h5Residual c bi cs g r s q hg hp hs hgtrue b (List.mem_toFinset.mp hmem)
    · exact Or.inr hexception
#print axioms solution
