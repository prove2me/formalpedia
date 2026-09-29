-- Prove2me | solution 1 for Freiman.section14_state_from_records
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:43:26.845975+00:00
-- url     : https://prove2.me/submissions/9d976960-03b1-4c41-ba1c-4a7f5daf327c

import Definitions.Def_Freiman_section14Model
import Mathlib.Tactic
open Freiman
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
private theorem complement_holds (b : CertBound) (r s q : ℝ)
    (h : ¬ certBoundHolds b r s q) : certBoundHolds (lowerHistoryComplement b) r s q := by
  rcases b with ⟨l,st,th⟩
  cases l <;> cases st <;> simpa [lowerHistoryComplement,certBoundHolds,not_le,not_lt] using h
private theorem negated_holds (bs : List CertBound) (v : LowerHistoryComparison) (r s q : ℝ)
    (hb : section14Holds bs r s q) (hv : ¬ section14ComparisonHolds v r s q) :
    section14Holds (section14NegatedConditions bs v) r s q := by
  cases v with
  | automatic => exact (hv trivial).elim
  | impossible => exact hb
  | bound b =>
    intro a ha
    simp only [section14NegatedConditions,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact complement_holds _ _ _ _ hv
    · exact hb _ ha
theorem solution (hr : ∀ (C : Section14Catalog) (si : ℕ) (rec : Section14Record), section14RecordValid C si rec → section14RecordSound C si rec) : ∀ (C : Section14Catalog) (si : ℕ), section14StateValid C si → section14StateSound C si := by
  intro C si hv pl hpl par hpar r s q hrect hbase gs hgs j hj hbranch
  have hpv := hv.2.2.2.2.1 pl hpl
  have hcov := hv.2.2.2.2.2.2 pl hpl par hpar
  rcases hcov with hex | hcov
  · obtain ⟨rec,hrec,hsi,hparrec,hgoal,hbi⟩ := hex
    have hsound := hr C si rec (hv.2.2.2.2.2.1 rec hrec hsi) par hpar hparrec r s q hrect
    apply False.elim
    apply hsound
    simpa [section14RecordConditions,hgoal,hbi,section14Branch,section14GoalBranches,
      hpv.2.1,hpv.2.2.2.1,section14NegatedConditions] using hbase
  · rcases hcov gs hgs j hj with ha | hrec
    · simp [section14ComparisonHolds,ha]
    · by_contra hn
      obtain ⟨rec,hm,hsi,hparrec,hgoal,hbi⟩ := hrec
      have hsound := hr C si rec (hv.2.2.2.2.2.1 rec hm hsi) par hpar hparrec r s q hrect
      apply hsound
      have hneg := negated_holds _ _ _ _ _ hbranch hn
      have hspec := hpv.2.2.2.2.2.2 gs hgs
      intro b hb
      simp only [section14RecordConditions,hgoal,hbi,hspec.1,List.mem_append] at hb
      rcases hb with (hb | hb) | hb
      · exact hbase b (List.mem_append_left _ hb)
      · exact hbase b (List.mem_append_right _ hb)
      · exact hneg b hb

#print axioms solution
