-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.coeff_gLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:19.544677+00:00
-- url     : https://prove2.me/submissions/ec840e78-45a7-4930-8efd-7275aee36d7f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
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
theorem _root_.solution (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ) :
    coeff n (gLog K l φ s) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  first
  | rfl
  | simp [gLog, coeff_apply]
end Formalism.L2.Th1.D.KernelCokernelKilling
