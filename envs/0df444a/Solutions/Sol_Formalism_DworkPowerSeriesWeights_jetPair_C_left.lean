-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_C_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:32.238699+00:00
-- url     : https://prove2.me/submissions/9968745c-ea36-40b3-b9da-f0240eba8d9f

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum

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
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (c : K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c) F = c * MvPowerSeries.constantCoeff F := by
  classical
  rw [jetPair_eq_sum (MvPolynomial.C c) F {0}]
  · simp [mfact, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro κ hκ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hκ
    rw [Finset.mem_singleton]
    by_contra h
    exact hκ (if_neg (fun h' => h h'.symm))
end Formalism.DworkPowerSeriesWeights
