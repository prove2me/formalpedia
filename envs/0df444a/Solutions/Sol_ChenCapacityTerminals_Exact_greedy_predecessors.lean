-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.greedy_predecessors
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:33.618836+00:00
-- url     : https://prove2.me/submissions/9d7ad649-69b3-42d6-8cd6-4edf66a00d6a

import Definitions.Def_ChenCapacityTerminals_Exact_Construction
import Theorems.Thm_ChenCapacityTerminals_Exact_greedy_cover_card_bound
import Theorems.Thm_ChenCapacityTerminals_Exact_full_group_incidences
import Theorems.Thm_ChenCapacityTerminals_Exact_unchanged_source_capacity

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
      (c : Construction), Prepared G r → 1 ≤ d → d ≤ G.vertices.card → 0 < L →
      LegalConstruction G r d L b t c →
      (c.greedy.toFinset.card : ℝ) ≤
        C * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) ∧
      (RootLowerBound G r L → ∀ A ∈ unchangedSources G r ((L : ℝ) / (4 * d))
          (c.partitions (c.rounds - 1)),
        3 * (L : ℝ) / (4 * d) ≤ weight G (c.greedy.toFinset \ A) A) := by
  refine ⟨2, by norm_num, ?_⟩
  intro G r d L b t c hprep hd hdn hL hc
  have hc' := hc
  rcases hc' with ⟨hround, hzero, hpart, hmerge, hfail, hstop, hrep,
    hjoinN, hjoin, hcomplete, hsort, hgreedy, hfinalN, hfinalTargets,
    hfinalWit, hret⟩
  have hgdata := full_group_incidences G r d L b t c hprep hd hdn hL hc
  dsimp only at hgdata
  have hsize := greedy_cover_card_bound G.vertices d
    ((unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1))).toList.flatMap fun A =>
        fullGroups d (c.tails A)) c.greedy hd hdn hgdata.1 hgreedy
  have hlog : Real.log (2 + (((unchangedSources G r ((L : ℝ) / (4 * d))
        (c.partitions (c.rounds - 1))).toList.flatMap fun A =>
          fullGroups d (c.tails A)).map Finset.card).sum) ≤
      Real.log (2 + (G.arcs.length : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_left hgdata.2 2
  constructor
  · exact hsize.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  · exact unchanged_source_capacity G r d L b t c hprep hd hdn hL hc
