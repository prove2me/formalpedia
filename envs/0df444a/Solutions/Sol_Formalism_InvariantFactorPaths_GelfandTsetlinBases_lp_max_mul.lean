-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_max_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.677614+00:00
-- url     : https://prove2.me/submissions/85a279b3-27f5-42ba-aef1-17af083b2f1a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_supp_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {A : Type*} [CommRing A] [IsDomain A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (x y : LaurentPolynomial A) :
    (x * y).coeff.support.max = x.coeff.support.max + y.coeff.support.max := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨a, ha⟩ := Finset.max_of_nonempty (lp_supp_nonempty hx)
  obtain ⟨b, hb⟩ := Finset.max_of_nonempty (lp_supp_nonempty hy)
  rw [ha, hb]
  have ha' := Finset.mem_of_max ha
  have hb' := Finset.mem_of_max hb
  have hc : (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
    apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
    intro a' b' ha'' hb'' h
    have h1 : a' ≤ a := Finset.le_max_of_eq ha'' ha
    have h2 : b' ≤ b := Finset.le_max_of_eq hb'' hb
    constructor <;> omega
  apply le_antisymm
  · apply Finset.max_le
    intro c hc'
    have := AddMonoidAlgebra.support_coeff_mul_subset x y hc'
    obtain ⟨a', ha'', b', hb'', rfl⟩ := Finset.mem_add.mp this
    have h1 : a' ≤ a := Finset.le_max_of_eq ha'' ha
    have h2 : b' ≤ b := Finset.le_max_of_eq hb'' hb
    rw [← WithBot.coe_add]
    exact WithBot.coe_le_coe.mpr (by omega)
  · rw [← WithBot.coe_add]
    apply Finset.le_max
    rw [Finsupp.mem_support_iff, hc]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha') (Finsupp.mem_support_iff.mp hb')
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
