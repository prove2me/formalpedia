-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.low_genLog_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:31:59.49016+00:00
-- url     : https://prove2.me/submissions/8a7a38c9-fe91-44e3-abe4-3c2f3d3122bf

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_genLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_genLogTrunc
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) (x : τ) (M : ℕ) :
    Low M (genLog (K := K) l p x - genLogTrunc l p x M) := by
  intro d hd
  rw [map_sub, coeff_genLog hl p x d hd, coeff_genLogTrunc, sub_self]
end Formalism.DworkPowerSeriesWeights
