-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hadamard_ideal_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:58.982404+00:00
-- url     : https://prove2.me/submissions/1249ed07-7956-4337-91f8-af9d0b771fda

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LocalIntegralStructure_denomNormFrac


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
theorem _root_.solution : HadamardIdeal := by
  intro E _ _ g t β J hg hβ hJ h
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.denomNormFrac E (β / (g : E) ^ t) J
    (div_ne_zero hβ (pow_ne_zero _ hgE)) hJ (by
      intro x hx; obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, by rw [div_mul_eq_mul_div, hy]; field_simp⟩)
  have hn : Algebra.norm ℚ ((g : E) ^ t) = (g : ℚ) ^ (t * finrank ℚ E) := by
    have : (g : E) ^ t = algebraMap ℚ E ((g : ℚ) ^ t) := by simp
    rw [this, Algebra.norm_algebraMap, ← pow_mul]
  have hpos : (0 : ℚ) < (g : ℚ) ^ (t * finrank ℚ E) := by positivity
  have hq : Algebra.norm ℚ (β / (g : E) ^ t) = Algebra.norm ℚ β / (g : ℚ) ^ (t * finrank ℚ E) := by
    rw [eq_div_iff hpos.ne', ← hn, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hgE)]
  rw [hq, abs_div, abs_of_pos hpos, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul] at h1
  exact h1
end Formalism.HermitianLatticeCounting.P
