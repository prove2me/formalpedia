-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.parity_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:45.936887+00:00
-- url     : https://prove2.me/submissions/1390228c-f1b2-4518-b0d0-a366b6b97279

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_val_sub_two
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)
open Formalism.L2.Th1.D.KernelCokernelKilling
open MvPowerSeries
variable {K : Type} [NormedField K] {τ : Type}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (t : ZMod d) :
    (t - 2).val % 2 = t.val % 2 := by
  obtain ⟨k, hk⟩ := val_sub_two t
  obtain ⟨j, hj⟩ := (even_iff_two_dvd.mp hd).mul_right k
  rw [hj] at hk
  omega
end Formalism.L2.Th1.D.KernelCokernelKilling
