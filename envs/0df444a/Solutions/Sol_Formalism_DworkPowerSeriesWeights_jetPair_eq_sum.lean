-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:36.638915+00:00
-- url     : https://prove2.me/submissions/e0a9321e-2d4b-4c40-90bf-401925269e02

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
theorem _root_.solution (P : MvPolynomial ι K) (F : MvPowerSeries ι K) (S : Finset (ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetPair P F =
      ∑ κ ∈ S, MvPolynomial.coeff κ P * ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  unfold jetPair
  refine Finset.sum_subset hS ?_
  intro κ _ hκ
  have h0 : MvPolynomial.coeff κ P = 0 := by simpa [MvPolynomial.mem_support_iff] using hκ
  simp [h0]
end Formalism.DworkPowerSeriesWeights
