-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bSlice_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:55:57.927965+00:00
-- url     : https://prove2.me/submissions/b92af5c8-a4b9-4395-8efd-a607884a5b24

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
variable {R : Type u} [CommRing R] {T σ ρ : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (e : T × σ → ρ) (he : Function.Injective e) (t : T) (κ : ρ →₀ ℕ) (y : σ) :
    bSlice e he t κ y = κ (e (t, y)) := rfl
end Formalism.DworkPowerSeriesWeights
