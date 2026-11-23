-- Prove2me | solution 1 for CompanionTheory.D.LK.comm_aa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:28.714804+00:00
-- url     : https://prove2.me/submissions/d3552d23-26b9-4b75-9694-0a3f55a7f720

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
theorem _root_.solution (haa : ∀ i j, an i * an j + an j * an i = 0) (l i j : Pos n) : an j * an i * an l = an l * (an j * an i) := by
  have h : ∀ i j, an i * an j = -(an j * an i) := fun i j => eq_neg_of_add_eq_zero_left (haa i j)
  rw [mul_assoc, h i l, mul_neg, ← mul_assoc, h j l, neg_mul, neg_neg, mul_assoc]
end CompanionTheory.D.LK
