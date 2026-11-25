-- Prove2me | solution 1 for Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.cc_xOfZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:04.646799+00:00
-- url     : https://prove2.me/submissions/72f09cbb-a9da-49c3-8c0b-5f7becebc8e1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TwoPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps
import Theorems.Thm_Formalism_L2_Th1_D_expSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries
namespace Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
theorem _root_.solution {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d] {l : ℕ}
    (hl : 2 ≤ l) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0) (x : PV ι N0 N1) :
    constantCoeff (xOfZ (d := d) l j σ om oms x) = 0 := by
  unfold xOfZ
  refine Pair.cc_ps ?_ (expSpec K l hl).1
  split_ifs <;>
    (rw [map_sum]; refine Finset.sum_eq_zero fun s _ => ?_; split_ifs <;> simp)
end Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
