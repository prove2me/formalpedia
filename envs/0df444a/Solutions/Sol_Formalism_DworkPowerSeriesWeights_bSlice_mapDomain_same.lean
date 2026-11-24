-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bSlice_mapDomain_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:28.93021+00:00
-- url     : https://prove2.me/submissions/f49cedf7-baab-4574-8ebd-250bae92d718

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bSlice_apply
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_injective_apply_prodMk_of_injective

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
theorem _root_.solution (e : T × σ → ρ) (he : Function.Injective e) (t : T) (u : σ →₀ ℕ) :
    bSlice e he t (u.mapDomain (fun y => e (t, y))) = u := by
  ext y
  rw [bSlice_apply]
  exact Finsupp.mapDomain_apply (injective_apply_prodMk_of_injective e he t) u y
end Formalism.DworkPowerSeriesWeights
