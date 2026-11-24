-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.map_gLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:12.635844+00:00
-- url     : https://prove2.me/submissions/189c83e8-3bd1-4f38-a506-41847cd560c5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Theorems.Thm_Formalism_L2_Th1_D_KernelCokernelKilling_coeff_gLog
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
variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution (ρ : K →+* K) (φ : ZMod d → τ) (s : ZMod d) :
    map ρ (gLog K l φ s) = gLog K l φ s := by
  ext n
  rw [coeff_map, coeff_gLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp
end Formalism.L2.Th1.D.KernelCokernelKilling
