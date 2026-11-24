-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.Lead_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:52.012938+00:00
-- url     : https://prove2.me/submissions/12e93349-5d56-46c7-9e6e-1ca1db8a32bb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_irrefl
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mon_LL

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (k : Type*) [CommRing k] {m : ℕ} (r c : Fin m → Fin n) (hr : StrictMono r)
    (hc : StrictMono c) : Lead key (((genX k n).submatrix r c).det) (mon r c 1) := by
  classical
  have hdet : ((genX k n).submatrix r c).det =
      ∑ π : Equiv.Perm (Fin m), C (((Equiv.Perm.sign π : ℤ) : k)) * monomial (mon r c π) (1 : k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_intCast]
    congr 1
    unfold mon
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [genX, Matrix.transpose_apply, Matrix.submatrix_apply, MvPolynomial.X]
  have hcoeff : ∀ e, coeff e (((genX k n).submatrix r c).det) =
      ∑ π : Equiv.Perm (Fin m), ((Equiv.Perm.sign π : ℤ) : k) * (if mon r c π = e then (1 : k) else 0) := by
    intro e
    rw [hdet, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  constructor
  · rw [hcoeff, Finset.sum_eq_single 1]
    · simp
    · intro π _ hπ
      rw [if_neg, mul_zero]
      intro h
      have := mon_LL hr hc π hπ
      rw [h] at this
      exact LL_irrefl _ _ this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro e he hne
    rw [MvPolynomial.mem_support_iff, hcoeff] at he
    obtain ⟨π, -, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hπe : mon r c π = e := by
      by_contra h
      exact hπ (by rw [if_neg h, mul_zero])
    subst hπe
    apply mon_LL hr hc π
    rintro rfl
    exact hne rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
