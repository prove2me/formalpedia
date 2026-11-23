-- Prove2me | solution 1 for Formalism.L2.Th1.D.KernelCokernelKilling.val_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:42.026227+00:00
-- url     : https://prove2.me/submissions/86e68c9a-bb70-40c0-86a6-ea6aabb1ba0b

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
variable {K : Type} [NormedField K] {τ : Type}
namespace Formalism.L2.Th1.D.KernelCokernelKilling
theorem _root_.solution {d : ℕ} [NeZero d] (t : ZMod d) :
    ∃ k : ℕ, (t - 2).val + 2 = t.val + d * k := by
  refine ⟨((t - 2).val + 2) / d, ?_⟩
  have h1 : (((t - 2).val + 2 : ℕ) : ZMod d) = ((t.val : ℕ) : ZMod d) := by
    first
    | simp
    | (push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_add_cancel])
    | (push_cast; simp)
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ d).mp h1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt t)] at h2
  have h3 := Nat.mod_add_div ((t - 2).val + 2) d
  rw [h2] at h3
  exact h3.symm
end Formalism.L2.Th1.D.KernelCokernelKilling
