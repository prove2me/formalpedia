-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.scalar_extension_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:18.884799+00:00
-- url     : https://prove2.me/submissions/08dac89f-507e-4172-9ef5-d7c836b8b62d

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
theorem _root_.solution : ScalarMore := by
  intro K _ t₁ t₂ D₁ D₂ R₁ R₂ h1 h2 hD hR
  have hiff : R₁ = 0 ↔ R₂ = 0 := by
    constructor
    · intro h; rw [h, mul_zero] at hR; exact (mul_eq_zero.mp hR.symm).resolve_left h2
    · intro h; rw [h, mul_zero] at hR; exact (mul_eq_zero.mp hR).resolve_left h1
  refine ⟨hiff, ?_⟩
  by_cases h : R₁ = 0
  · rw [h, hiff.mp h]; simp
  · have h' : R₂ ≠ 0 := fun e => h (hiff.mpr e)
    rw [div_eq_div_iff h h']
    have : t₁ * t₂ * (D₁ * R₂ - D₂ * R₁) = 0 := by linear_combination t₂ * R₂ * hD - t₂ * D₂ * hR
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero h1 h2)
    linear_combination this
end Formalism.HermitianLatticeCounting.P
