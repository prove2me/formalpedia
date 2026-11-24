-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bM_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:59.873215+00:00
-- url     : https://prove2.me/submissions/3c73b950-299b-447b-beb5-81c7c00a9a38

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
theorem _root_.solution (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ, (x τ).det ≠ 0) (t : H) :
    bM x (false, t) * (bM x (true, t)).transpose = 1 := by
  simp only [bM, if_true, Matrix.transpose_transpose]
  simpa using Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hx (false, t)))
end Formalism.DworkPowerSeriesWeights
