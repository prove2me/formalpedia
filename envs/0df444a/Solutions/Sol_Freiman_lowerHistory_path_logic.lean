-- Prove2me | solution 1 for Freiman.lowerHistory_path_logic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:05.375022+00:00
-- url     : https://prove2.me/submissions/664a3908-71b0-41dd-8781-9d77c25e8cbc

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

private theorem at_conditions_append (as bs : List CertBound) (r s q : ℝ)
    (ha : lowerHistoryConditions as r s q) (hb : lowerHistoryConditions bs r s q) :
    lowerHistoryConditions (as ++ bs) r s q := by
  intro b hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha b hm
  · exact hb b hm

private theorem at_conditions_eraseDups (bs : List CertBound) (r s q : ℝ)
    (hb : lowerHistoryConditions bs r s q) :
    lowerHistoryConditions bs.eraseDups r s q := by
  intro b hm
  exact hb b (List.mem_eraseDups.mp hm)

private theorem at_conditions_singleton (b : CertBound) (r s q : ℝ)
    (hb : certBoundHolds b r s q) : lowerHistoryConditions [b] r s q := by
  intro c hc
  have hcb : c = b := List.mem_singleton.mp hc
  subst c
  exact hb

theorem solution (hneg : ∀ (b : CertBound) (r s q : ℝ), certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q) (p : LowerHistoryPath) (hb : lowerHistoryPathBinding p)
    (r s q : ℝ) (hsource : ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryConditions bs r s q)
    (hex : ∀ record ∈ lowerHistoryRecordsFor p, record.survivor = false →
      ¬ lowerHistoryConditions (lowerHistoryResidual p record.alternative record.endpointBranch) r s q) :
    (p.catalog = .initial ∧ lowerHistorySurvivor p) ∨
      (p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p r s q) := by
  classical
  obtain ⟨bs, hbs, htrue⟩ := hsource
  obtain ⟨ai, hai⟩ := List.mem_iff_getElem?.mp hbs
  obtain ⟨haiBound, _⟩ := List.getElem?_eq_some_iff.mp hai
  rcases hb.2.2 ai haiBound with hnegative | hcomparisons
  · obtain ⟨record, hmem, halternative, hbranch⟩ := hnegative
    cases hsurvivor : record.survivor with
    | false =>
        exact False.elim (hex record hmem hsurvivor (by
          simpa [lowerHistoryResidual, halternative, hbranch, hai] using htrue))
    | true =>
        have hrecord : lowerHistorySurvivor p ∧ record.alternative = 0 := by
          simpa [lowerHistoryRecordBinding, hsurvivor] using hb.2.1 record hmem
        exact Or.inl ⟨hrecord.1.1, hrecord.1⟩
  · obtain ⟨hcatalog, hrow, hcoverage⟩ := hcomparisons
    refine Or.inr ⟨hcatalog, hrow, ?_⟩
    intro cg hcg hconditions
    by_contra hfailed
    have hnotautomatic : cg.2 ≠ .automatic := by
      intro hautomatic
      apply hfailed
      simp [lowerHistoryComparisonHolds, hautomatic]
    obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hcg
    obtain ⟨record, hmem, halternative, hbranch, hsurvivor⟩ :=
      hcoverage bi cg.1 cg.2 hbi hnotautomatic
    apply hex record hmem hsurvivor
    have hresidual : lowerHistoryResidual p record.alternative record.endpointBranch =
        ((bs ++ cg.1) ++ (match cg.2 with
          | .bound b => [lowerHistoryComplement b]
          | _ => [])).eraseDups := by
      have hnonneg : ¬ (bi : ℤ) < 0 := by omega
      cases hcomparison : cg.2 <;>
        simp [lowerHistoryResidual, halternative, hbranch, hai, hbi, hnonneg, hcomparison] <;>
        rfl
    rw [hresidual]
    apply at_conditions_eraseDups
    apply at_conditions_append (bs ++ cg.1) _ r s q
    · exact at_conditions_append bs cg.1 r s q htrue hconditions
    · cases hg : cg.2 with
      | automatic => exact False.elim (hnotautomatic hg)
      | impossible =>
          intro b hmem
          simp at hmem
      | bound b =>
          apply at_conditions_singleton
          apply (hneg b r s q).mpr
          simpa [lowerHistoryComparisonHolds, hg] using hfailed

#print axioms solution
