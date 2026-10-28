-- Prove2me | solution 1 for ContinuumHypothesis.goedel_consistency_AC_GCH
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T23:15:08.243069+00:00
-- url     : https://prove2.me/submissions/ca368217-0f29-4cbe-8d59-2a093332b6c9

import Theorems.Thm_ContinuumHypothesis_Constructible_models_ZF
import Theorems.Thm_ContinuumHypothesis_Constructible_models_AC
import Theorems.Thm_ContinuumHypothesis_Constructible_models_GCH

open FirstOrder FirstOrder.Language ContinuumHypothesis
open ContinuumHypothesis.Constructible

-- This sketch uses the external constructible universe in Lean's metatheory.
-- The three imported model assertions are the remaining mathematical obligations.
theorem solution (hZF : ZF.IsSatisfiable) :
    (ZFC ∪ {gchSentence}).IsSatisfiable := by
  have hAC : Carrier ⊨ ({acSentence} : setLang.Theory) :=
    Theory.model_singleton_iff.mpr models_AC
  have hGCH : Carrier ⊨ ({gchSentence} : setLang.Theory) :=
    Theory.model_singleton_iff.mpr models_GCH
  haveI : Carrier ⊨ ZFC ∪ {gchSentence} :=
    (models_ZF.union hAC).union hGCH
  exact Theory.Model.isSatisfiable Carrier
