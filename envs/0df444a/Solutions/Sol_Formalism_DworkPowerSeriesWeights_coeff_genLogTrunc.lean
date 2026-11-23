-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.coeff_genLogTrunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:10.840906+00:00
-- url     : https://prove2.me/submissions/45b783e6-a1bc-492f-be59-86aaa0daca92

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
theorem _root_.solution (l : ℕ) (p : τ → τ) (x : τ) (M : ℕ) (n : τ →₀ ℕ) :
    coeff n (genLogTrunc (K := K) l p x M) = ∑ e ∈ Finset.range M,
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  simp only [genLogTrunc, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
end Formalism.DworkPowerSeriesWeights
