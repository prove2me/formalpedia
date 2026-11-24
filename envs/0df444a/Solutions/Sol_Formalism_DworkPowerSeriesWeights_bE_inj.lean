-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bE_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:15.351419+00:00
-- url     : https://prove2.me/submissions/6006c93c-e4d6-4f69-9722-c6a5f36adf3b

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (H : Type) (N0 N1 : ℕ) : Function.Injective (bE H N0 N1) := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
  simp only [bE, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl
end Formalism.DworkPowerSeriesWeights
