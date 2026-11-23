-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.iter_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:40.523792+00:00
-- url     : https://prove2.me/submissions/11816efd-6366-4bad-a348-1d2db2417f7d

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
theorem _root_.solution {α : Type} {d : ℕ} [NeZero d] (f : α → α) {c : α} (hc : f^[d] c = c)
    (t : ZMod d) : f (f (f^[(t - 2).val] c)) = f^[t.val] c := by
  obtain ⟨k, hk⟩ := val_sub_two t
  have h1 : f (f (f^[(t - 2).val] c)) = f^[(t - 2).val + 2] c := by
    first
    | (rw [add_comm, Function.iterate_add_apply]; rfl)
    | simp only [Function.iterate_succ_apply']
  rw [h1, hk, Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hc]
end Formalism.L2.Th1.D.KernelCokernelKilling
