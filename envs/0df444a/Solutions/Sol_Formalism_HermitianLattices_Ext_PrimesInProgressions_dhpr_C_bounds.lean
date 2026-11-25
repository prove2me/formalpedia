-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_C_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:02.452384+00:00
-- url     : https://prove2.me/submissions/6883edee-4902-449d-a188-6a7a28fff96e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : 0 ≤ dhprC χ₁ n ∧ dhprC χ₁ n ≤ 2 := by
  unfold dhprC
  by_cases hu : IsUnit (n : ZMod M)
  · have h2 : χ₁ (n : ZMod M) ^ 2 = 1 := by
      have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
      simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
      simpa using e
    have h3 : χ₁ (n : ZMod M) = 1 ∨ χ₁ (n : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
    rw [MulChar.one_apply hu]
    rcases h3 with h3 | h3 <;> rw [h3] <;> norm_num
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    norm_num
end Formalism.HermitianLattices.Ext.PrimesInProgressions
