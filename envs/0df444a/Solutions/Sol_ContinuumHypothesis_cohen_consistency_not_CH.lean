-- Prove2me | solution 1 for ContinuumHypothesis.cohen_consistency_not_CH
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T02:17:08.744521+00:00
-- url     : https://prove2.me/submissions/88527e6f-6aa8-4ec7-af09-a8957500f192

import Theorems.Thm_ContinuumHypothesis_Cohen_expanded_countermodel_exists
import Theorems.Thm_ContinuumHypothesis_Cohen_membership_reduct_models_ZFC
import Theorems.Thm_ContinuumHypothesis_Cohen_ch_sentence_implies_expanded_CH

open FirstOrder FirstOrder.Language ContinuumHypothesis

/-!
**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This is a reduction with two open semantic-translation obligations.
-/

theorem solution (hZFC : ContinuumHypothesis.ZFC.IsSatisfiable) :
    (ContinuumHypothesis.ZFC ∪ {∼chSentence}).IsSatisfiable := by
  obtain ⟨M, hM, hExpanded, hNot⟩ := Cohen.expanded_countermodel_exists
  letI : Nonempty M.carrier := hM
  letI : setLang.Structure M.carrier := Cohen.membershipReduct M
  have hZ : M.carrier ⊨ ContinuumHypothesis.ZFC :=
    Cohen.membership_reduct_models_ZFC M hM hExpanded
  have hNeg : M.carrier ⊨ ∼chSentence := by
    rw [Sentence.realize_not]
    exact fun hCH => hNot (Cohen.ch_sentence_implies_expanded_CH M hM hExpanded hCH)
  haveI : M.carrier ⊨ ContinuumHypothesis.ZFC ∪ {∼chSentence} :=
    hZ.union (Theory.model_singleton_iff.mpr hNeg)
  exact Theory.Model.isSatisfiable M.carrier
