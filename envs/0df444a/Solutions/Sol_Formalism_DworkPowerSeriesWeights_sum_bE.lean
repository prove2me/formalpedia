-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_bE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:36.71898+00:00
-- url     : https://prove2.me/submissions/af3778af-db4e-476a-9a63-2198eb86c280

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
theorem _root_.solution [Fintype H] {N1 : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Bool × H × Fin N0 × Fin N1 → M) : ∑ y, f y = ∑ w, f (bE H N0 N1 w) :=
  (Equiv.sum_comp (Equiv.prodAssoc Bool H (Fin N0 × Fin N1)) f).symm
end Formalism.DworkPowerSeriesWeights
