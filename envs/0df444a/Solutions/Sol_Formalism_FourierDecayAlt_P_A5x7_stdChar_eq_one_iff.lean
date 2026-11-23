-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.stdChar_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:45.475262+00:00
-- url     : https://prove2.me/submissions/64d56269-8c1d-4be5-b5a9-a707601728d1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_stdChar_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (x : ℚ_[p]) : stdChar p x = 1 ↔ ‖x‖ ≤ 1 := by
  rw [stdChar_apply, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hq : fr p x = n := by
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have h3 : ((fr p x : ℚ) : ℂ) = ((n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ h2
        rw [hn]
        ring
      exact_mod_cast h3
    calc ‖x‖ = ‖(x - ((fr p x : ℚ) : ℚ_[p])) + ((n : ℤ) : ℚ_[p])‖ := by
          rw [hq, Rat.cast_intCast, sub_add_cancel]
      _ ≤ max ‖x - ((fr p x : ℚ) : ℚ_[p])‖ ‖((n : ℤ) : ℚ_[p])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (fr_norm p x) (Padic.norm_int_le_one n)
  · intro hx
    have hn : ‖((fr p x : ℚ) : ℚ_[p])‖ ≤ 1 := by
      calc ‖((fr p x : ℚ) : ℚ_[p])‖ = ‖x - (x - ((fr p x : ℚ) : ℚ_[p]))‖ := by
            rw [sub_sub_cancel]
        _ ≤ max ‖x‖ ‖x - ((fr p x : ℚ) : ℚ_[p])‖ := by
            rw [sub_eq_add_neg]
            exact (Padic.nonarchimedean _ _).trans_eq (by rw [norm_neg])
        _ ≤ 1 := max_le hx (fr_norm p x)
    obtain ⟨z, hz⟩ := inS_int p (fr_inS p x) hn
    exact ⟨z, by rw [hz]; push_cast; ring⟩
end Formalism.FourierDecayAlt.P.A5x7
