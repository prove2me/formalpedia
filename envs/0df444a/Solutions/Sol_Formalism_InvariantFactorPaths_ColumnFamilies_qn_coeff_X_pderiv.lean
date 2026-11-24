-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_coeff_X_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:52.037121+00:00
-- url     : https://prove2.me/submissions/8f629b7d-78d4-4a6a-a0e9-fcc03efb39eb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {σ : Type*} (i : σ) (f : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    coeff m (X i * pderiv i f) = (m i : ℚ) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    have h : X i * pderiv i (monomial s c) = (s i : ℚ) • monomial s c := by
      rw [pderiv_monomial]
      by_cases hs : s i = 0
      · simp [hs]
      · have h1 : Finsupp.single i 1 + (s - Finsupp.single i 1) = s :=
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs))
        rw [X, monomial_mul, h1, smul_monomial, one_mul, smul_eq_mul, mul_comm]
    rw [h, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with hsm
    · rw [hsm]
    · simp
  | add p q hp hq => rw [map_add, mul_add, coeff_add, coeff_add, hp, hq, mul_add]
end Formalism.InvariantFactorPaths.ColumnFamilies
