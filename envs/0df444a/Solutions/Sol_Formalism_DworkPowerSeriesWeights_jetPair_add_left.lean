-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:49.482646+00:00
-- url     : https://prove2.me/submissions/daa4f6e9-4f1e-4b72-bd51-b3d6956ee119

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
theorem _root_.solution (P Q : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair (P + Q) F = jetPair P F + jetPair Q F := by
  classical
  rw [jetPair_eq_sum (P + Q) F (P.support ∪ Q.support) MvPolynomial.support_add,
    jetPair_eq_sum P F (P.support ∪ Q.support) Finset.subset_union_left,
    jetPair_eq_sum Q F (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring
end Formalism.DworkPowerSeriesWeights
