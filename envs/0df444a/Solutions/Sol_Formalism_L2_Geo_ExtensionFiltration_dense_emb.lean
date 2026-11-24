-- Prove2me | solution 1 for Formalism.L2.Geo.ExtensionFiltration.dense_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:19.868204+00:00
-- url     : https://prove2.me/submissions/6175eda6-6538-4dd2-b242-f1e54a6cc6be

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_PDescentCutA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
set_option linter.deprecated false
open Module NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.ExtensionFiltration
namespace Formalism.L2.Geo.ExtensionFiltration
theorem _root_.solution {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  have hs := (NumberField.InfinitePlace.Completion.bijective_extensionEmbedding_of_isComplex hv).2
  have hc : Continuous (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
  have h := hs.denseRange.comp (NumberField.InfinitePlace.Completion.denseRange_coe v) hc
  refine Dense.mono ?_ h
  rintro _ ⟨x, rfl⟩
  first
    | (refine ⟨WithAbs.equiv _ x, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)
    | (refine ⟨WithAbs.ofAbs x, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)
    | (refine ⟨x.1, ?_⟩
       first
        | exact (NumberField.InfinitePlace.Completion.extensionEmbedding_coe v x).symm
        | simp [NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
        | rfl)
end Formalism.L2.Geo.ExtensionFiltration
