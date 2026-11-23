-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:03.773518+00:00
-- url     : https://prove2.me/submissions/02e17aa9-9a48-464f-a080-ae353a4e2ea4

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
theorem _root_.solution (κ : ι →₀ ℕ) (c : MvPolynomial σ K) (Th : MvPowerSeries ι K) :
    jetPairPoly (MvPolynomial.monomial κ c) Th =
      c * MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  classical
  rw [jetPairPoly_eq_sum _ Th {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]
end Formalism.DworkPowerSeriesWeights.OrbMul
