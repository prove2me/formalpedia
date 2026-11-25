-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.subst_genLogTrunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:43.1969+00:00
-- url     : https://prove2.me/submissions/0ced95bd-7b48-4a5e-a6bf-d2f90bef2c69

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
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
theorem _root_.solution [Finite τ] {g : τ → MvPowerSeries τ K} (hs : HasSubst g) (l : ℕ)
    (p : τ → τ) (x : τ) (M : ℕ) :
    subst g (genLogTrunc (K := K) l p x M) =
      ∑ e ∈ Finset.range M, ((l : K) ^ e)⁻¹ • (g (p^[e] x)) ^ ((l ^ 2) ^ e) := by
  rw [← MvPowerSeries.coe_substAlgHom hs]
  simp only [genLogTrunc, map_sum, map_smul, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs]
end Formalism.DworkPowerSeriesWeights
