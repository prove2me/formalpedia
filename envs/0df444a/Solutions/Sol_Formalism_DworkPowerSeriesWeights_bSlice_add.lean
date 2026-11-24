-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bSlice_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:27.556377+00:00
-- url     : https://prove2.me/submissions/3f84db2c-8df1-4061-8ce0-54b8d2723a8c

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_apply

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
theorem _root_.solution (e : T × σ → ρ) (he : Function.Injective e) (t : T) (a b : ρ →₀ ℕ) :
    bSlice e he t (a + b) = bSlice e he t a + bSlice e he t b := by
  ext y
  simp [bSlice_apply]
end Formalism.DworkPowerSeriesWeights
