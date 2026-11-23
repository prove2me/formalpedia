-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.range_first_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:28.527298+00:00
-- url     : https://prove2.me/submissions/fe0354e2-428e-4431-b03a-ad0a985155f6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_seg_eB
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eB_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (i : D.ML) : (∃ k, D.e0 j k = i) ↔
    (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨D.eB j a, D.seg_eB j a, by simp⟩
    | right m => exact Or.inr ⟨Fin.rev m, by simp⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m, rfl⟩)
    · obtain ⟨a, rfl⟩ := D.eB_surj j b hb
      exact ⟨Fin.castAdd D.r a, by simp⟩
    · exact ⟨Fin.natAdd (D.nB j) (Fin.rev m), by simp⟩
end Formalism.MainNotions.PlaneGram.TwistData
