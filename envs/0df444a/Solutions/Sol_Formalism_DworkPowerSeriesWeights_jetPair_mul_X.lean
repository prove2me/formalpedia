-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:07.845168+00:00
-- url     : https://prove2.me/submissions/17ac6a85-7deb-4561-bd2b-58552cb4bd39

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single

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
theorem _root_.solution (P : MvPolynomial ι K) (i : ι) (F : MvPowerSeries ι K) :
    jetPair (P * MvPolynomial.X i) F = jetPair P (MvPowerSeries.pderiv K i F) := by
  classical
  rw [jetPair, MvPolynomial.support_mul_X, Finset.sum_map, jetPair]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  simp only [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, mfact_add_single,
    MvPowerSeries.coeff_pderiv]
  push_cast
  ring
end Formalism.DworkPowerSeriesWeights
