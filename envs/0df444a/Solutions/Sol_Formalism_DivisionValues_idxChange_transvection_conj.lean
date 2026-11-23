-- Prove2me | solution 1 for Formalism.DivisionValues.idxChange_transvection_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:00.190021+00:00
-- url     : https://prove2.me/submissions/1e2d22f0-73b5-4a7b-a0a1-bcde0ac9b0e8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution {i j : Fin d} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    Matrix.transvection i j c =
      idxChangeDg i c * Matrix.transvection i j (1 : K) * idxChangeDg i c⁻¹ := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.transvection, hij, Function.update_of_ne (Ne.symm hij)]
  · have hs : ∀ x : K, Matrix.single i j x a b = 0 := by
      intro x
      rw [Matrix.single_apply]
      split_ifs with h'
      · exact absurd ⟨h'.1.symm, h'.2.symm⟩ h
      · rfl
    simp only [Matrix.transvection, Matrix.add_apply, hs, add_zero]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = i
      · subst ha; simp [hc]
      · simp [Function.update_of_ne ha]
    · simp [hab]
end Formalism.DivisionValues
