-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.linOL_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:59.84895+00:00
-- url     : https://prove2.me/submissions/bbe0f017-0cc7-4427-be2f-4ea189256cc3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_iter_odd

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D.InverseCommuting
variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.InverseCommuting
theorem _root_.solution (σ : K →+* K) {ι : Type} [Fintype ι] (a y : ι → K)
    (ha : ∀ i, σ (σ (a i)) = a i) (L : ZMod d → MvPowerSeries τ K) :
    linOL σ (∑ i, a i * y i) L = ∑ i, C (σ (a i)) * linOL σ (y i) L := by
  unfold linOL
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp only [if_pos hs]
    simp
  · simp only [if_neg hs]
    rw [← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RingHom.coe_pow, iter_odd (ha i) hs, map_mul]
    ring
end Formalism.L2.Th1.D.InverseCommuting
