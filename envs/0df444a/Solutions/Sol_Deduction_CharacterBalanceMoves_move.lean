-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:04.602235+00:00
-- url     : https://prove2.me/submissions/0403d191-330a-4a5e-95cf-1f680086b6e6

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalanceMoves
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x Cd y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (ψ : AddChar (E0 × H) ℂ) (hψ0 : ψ ≠ 0) :
    ‖GPsi D ell ψ y - GPsi D ell ψ x‖ ≤ Real.log (x + 1) + Cd + ‖ell ψ‖ := by
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hd := hDer.1 ψ hψ0 y x (by linarith) (by linarith)
  have hmax : max y x ≤ x + 1 := max_le (by linarith) (by linarith)
  have hmax1 : 1 ≤ max y x := le_trans (by linarith) (le_max_right y x)
  have hlog : Real.log (max y x) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hmax
  have hlog0 : 0 ≤ Real.log (max y x) := Real.log_nonneg hmax1
  have hs : 0 ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by positivity
  have h1 := mul_le_mul_of_nonneg_right hy hs
  linarith
end Deduction.CharacterBalanceMoves
