-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.final_constant_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:17.297887+00:00
-- url     : https://prove2.me/submissions/fe8452e8-8db3-446a-81a0-4de0884ee6ac

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ConstFinal := by
  intro r th st hth hst0 hst
  have h1 : (1 / 2 : ℝ) ^ (2 * r) ≤ th ^ (2 * r) := pow_le_pow_left₀ (by norm_num) hth _
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * r) := by positivity
  have h2 : (th ^ (2 * r))⁻¹ ≤ ((1 / 2 : ℝ) ^ (2 * r))⁻¹ := inv_anti₀ hp h1
  have h3 : ((1 / 2 : ℝ) ^ (2 * r))⁻¹ = 2 ^ r * 2 ^ r := by
    rw [← inv_pow, two_mul, pow_add]; norm_num
  rw [h3] at h2
  have h4 : 0 ≤ (th ^ (2 * r))⁻¹ := by positivity
  have h5 : (0 : ℝ) < 2 ^ r := by positivity
  calc ((2 : ℝ) ^ (r + 1))⁻¹ * (th ^ (2 * r))⁻¹ * st
      ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * (2 ^ r * 2 ^ r) * 3 := by gcongr
    _ = 3 * (2 : ℝ) ^ r / 2 := by rw [pow_succ]; field_simp
end Formalism.HermitianLatticeCounting.P
