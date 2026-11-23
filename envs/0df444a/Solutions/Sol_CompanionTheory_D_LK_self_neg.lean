-- Prove2me | solution 1 for CompanionTheory.D.LK.self_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:40.499776+00:00
-- url     : https://prove2.me/submissions/2d20a9ff-36d4-47b1-90c8-d3220d79bfd5

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator

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
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)
namespace CompanionTheory.D.LK
theorem _root_.solution {x : R} (h : x = -x) : x = 0 := by
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h
  rw [← one_smul ℂ x, ← inv_mul_cancel₀ (two_ne_zero' ℂ), mul_smul, this, smul_zero]
end CompanionTheory.D.LK
