-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:04.822843+00:00
-- url     : https://prove2.me/submissions/1a9fab8c-034d-4807-a4ac-eda8522b6e1a

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
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x Cd : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hDer : DerivInt D ell Cd) (ψ : AddChar (E0 × H) ℂ) (hψ0 : ψ ≠ 0) :
    ‖GPsi D ell ψ x‖ ≤ x * (Real.log x + Cd + ‖ell ψ‖) := by
  have hd := hDer.1 ψ hψ0 x 1 (by linarith) le_rfl
  have h1 : GPsi D ell ψ 1 = ell ψ := by
    unfold GPsi
    rw [if_neg hψ0]
    simp
  rw [h1, max_eq_left (by linarith), abs_of_nonneg (by linarith)] at hd
  have h2 : ‖GPsi D ell ψ x‖ ≤ ‖GPsi D ell ψ x - ell ψ‖ + ‖ell ψ‖ := by
    simpa using norm_add_le (GPsi D ell ψ x - ell ψ) (ell ψ)
  have h3 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith
end Deduction.CharacterBalanceMoves
