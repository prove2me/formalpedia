-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bM_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:59.074283+00:00
-- url     : https://prove2.me/submissions/116c3676-6d85-4923-a13b-01864f7a3841

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_inv_entry_le_one


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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ i a, ‖x τ i a‖ ≤ 1)
    (hdet : ∀ τ, ‖(x τ).det‖ = 1) (τ : Bool × H) (i a : Fin N0) : ‖bM x τ i a‖ ≤ 1 := by
  unfold bM
  split_ifs
  · rw [Matrix.transpose_apply]
    exact norm_inv_entry_le_one _ (hx _) (hdet _) _ _
  · exact hx _ _ _
end Formalism.DworkPowerSeriesWeights
