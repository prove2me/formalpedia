-- Prove2me | solution 1 for ContinuumHypothesis.ch_independent_of_ZFC
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-22T10:50:57.623042+00:00
-- url     : https://prove2.me/submissions/68ec8837-329f-49ca-b538-263310ec6862
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Prove2Me proof-sketch prepared for Wentao Li.

This reduction uses the mission's existing open Gödel, GCH-to-CH, and Cohen
milestones. Their proofs remain separate obligations; the reduction below
contains no proof holes and does not import its own target.
-/
import Theorems.Thm_ContinuumHypothesis_goedel_consistency_AC_GCH
import Theorems.Thm_ContinuumHypothesis_gch_sentence_implies_ch_sentence
import Theorems.Thm_ContinuumHypothesis_cohen_consistency_not_CH

open FirstOrder FirstOrder.Language ContinuumHypothesis

theorem solution (hZFC : ZFC.IsSatisfiable) :
    ¬ ZFC ⊨ᵇ chSentence ∧ ¬ ZFC ⊨ᵇ ∼chSentence := by
  constructor
  · intro hCH
    exact (Theory.models_iff_not_satisfiable chSentence).mp hCH
      (cohen_consistency_not_CH hZFC)
  · intro hNotCH
    have hZF : ZF.IsSatisfiable :=
      hZFC.mono (show ZF ⊆ ZFC from Set.subset_union_left)
    let M := (goedel_consistency_AC_GCH hZF).some
    haveI : M ⊨ ZFC :=
      Theory.Model.mono M.is_model Set.subset_union_left
    have hCH : M ⊨ chSentence :=
      gch_sentence_implies_ch_sentence.realize_sentence M
    have hNotCHM : M ⊨ ∼chSentence := hNotCH.realize_sentence M
    exact (Sentence.realize_not M).mp hNotCHM hCH
