-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.linEL_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:41.741354+00:00
-- url     : https://prove2.me/submissions/09417d38-ea8a-4996-b794-47c4259c234e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_L2_Th1_D_InverseCommuting_iter_even

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
    linEL σ (∑ i, a i * y i) L = ∑ i, C (a i) * linEL σ (y i) L := by
  unfold linEL
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp only [if_pos hs]
    rw [← RingHom.coe_pow, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RingHom.coe_pow, iter_even (ha i) hs, map_mul]
    ring
  · simp only [if_neg hs]
    simp
end Formalism.L2.Th1.D.InverseCommuting
