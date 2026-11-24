-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.min_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:34.372947+00:00
-- url     : https://prove2.me/submissions/f074bcdd-106a-443e-aba4-775aaea9d9fb

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ : Type} [Fintype σ] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) ≤ ∑ y, u y :=
  Finset.sum_le_sum fun _ _ => min_le_left _ _
end Formalism.DworkPowerSeriesWeights
