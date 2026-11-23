-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:49.592009+00:00
-- url     : https://prove2.me/submissions/1fc1c4fd-2919-4ab0-9f8e-4fe6d3333641

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
theorem _root_.solution (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.C c * P) F = c * jetPair P F := by
  classical
  rw [jetPair_eq_sum (MvPolynomial.C c * P) F P.support, jetPair, Finset.mul_sum]
  · refine Finset.sum_congr rfl (fun κ _ => ?_)
    rw [MvPolynomial.coeff_C_mul]
    ring
  · intro κ hκ
    rw [MvPolynomial.mem_support_iff] at hκ ⊢
    rw [MvPolynomial.coeff_C_mul] at hκ
    exact right_ne_zero_of_mul hκ
end Formalism.DworkPowerSeriesWeights
