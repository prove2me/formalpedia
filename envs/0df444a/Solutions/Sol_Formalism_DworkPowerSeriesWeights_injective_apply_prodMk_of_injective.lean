-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.injective_apply_prodMk_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:58.290496+00:00
-- url     : https://prove2.me/submissions/15e03264-17ba-439a-a683-adf19bcb144e

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj


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
theorem _root_.solution (e : T × σ → ρ) (he : Function.Injective e) (t : T) :
    Function.Injective (fun y : σ => e (t, y)) :=
  fun _ _ h => (Prod.mk.inj (he h)).2
end Formalism.DworkPowerSeriesWeights
