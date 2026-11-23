-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:20.543698+00:00
-- url     : https://prove2.me/submissions/c33644aa-3476-49dc-a2f0-761638fcb177

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul

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
theorem _root_.solution (P : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K)
    (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    jetPairPoly P Th = ∑ κ ∈ S, MvPolynomial.coeff κ P *
      MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  unfold jetPairPoly
  refine Finset.sum_subset hS fun κ _ hκ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
end Formalism.DworkPowerSeriesWeights.OrbMul
