-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hypothesis_additivity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:02.7817+00:00
-- url     : https://prove2.me/submissions/fed3217b-002b-4a1e-bd3e-e4a64814a994

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
theorem _root_.solution : HypAdd := by
  intro ch₁ sh₁ ch₂ sh₂ x h1 h2 hc1 hc2 e1 e2 hx hle
  have hy : ch₁ / sh₁ * (ch₂ / sh₂) + 1 / sh₁ * (1 / sh₂) = (ch₁ * ch₂ + 1) / (sh₁ * sh₂) := by
    field_simp
  rw [hy] at hle
  have hsq : x ^ 2 ≤ ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2 := pow_le_pow_left₀ hx hle 2
  have : ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2 - 1 = ((ch₁ + ch₂) / (sh₁ * sh₂)) ^ 2 := by
    rw [div_pow, div_pow]
    have hne : (sh₁ * sh₂) ^ 2 ≠ 0 := by positivity
    rw [div_sub_one hne]
    congr 1
    linear_combination (ch₂ ^ 2 - 1) * e1 + sh₁ ^ 2 * e2
  linarith
end Formalism.HermitianLatticeCounting.P
