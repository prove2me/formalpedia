-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:41.673078+00:00
-- url     : https://prove2.me/submissions/68a63fee-158f-482d-a32b-9ae6063d8d36

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
theorem _root_.solution (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) :
    coeff n (gLog K l φ s) = 0 := by
  rw [coeff_gLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)
end Formalism.L2.Th1.D.KernelCokernelKilling
