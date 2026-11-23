-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:03.167363+00:00
-- url     : https://prove2.me/submissions/7cb839d8-70bb-4d54-b573-29d03bb00baa

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_jetPairPoly_eq_sum

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OrbMul
variable {K : Type} [Field K] {σ ι : Type}
namespace Formalism.DworkPowerSeriesWeights.OrbMul
theorem _root_.solution (P Q : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K) :
    jetPairPoly (P + Q) Th = jetPairPoly P Th + jetPairPoly Q Th := by
  classical
  rw [jetPairPoly_eq_sum (P + Q) Th (P.support ∪ Q.support) MvPolynomial.support_add,
    jetPairPoly_eq_sum P Th (P.support ∪ Q.support) Finset.subset_union_left,
    jetPairPoly_eq_sum Q Th (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]
end Formalism.DworkPowerSeriesWeights.OrbMul
