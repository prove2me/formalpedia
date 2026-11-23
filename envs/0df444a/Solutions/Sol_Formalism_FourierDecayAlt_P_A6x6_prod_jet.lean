-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x6.prod_jet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:09.660501+00:00
-- url     : https://prove2.me/submissions/79b007ce-fa9a-47a8-ba28-3ecc24b17729

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_X_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_e_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_p_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_two_half
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open MvPolynomial
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A6x6
theorem _root_.solution (s : Finset (Fin m)) :
    (∏ k ∈ s, (1 + X k) - (1 + ∑ k ∈ s, X k + C (1 / 2 : ℚ) *
      ((∑ k ∈ s, X k) ^ 2 - ∑ k ∈ s, X k ^ 2)) : MvPolynomial (Fin m) ℚ) ∈
      idealOfVars (Fin m) ℚ ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : (X a * (C (1 / 2 : ℚ) * ((∑ k ∈ s, X k) ^ 2 - ∑ k ∈ s, X k ^ 2)) :
        MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ ^ 3 := by
      rw [pow_succ' _ 2]
      exact Ideal.mul_mem_mul (X_mem a)
        (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.pow_mem_pow (e_mem s) 2) (p_mem s)))
    have h2 := Ideal.add_mem _ (Ideal.mul_mem_left _ (1 + X a) ih) h1
    convert h2 using 1
    linear_combination (-((∑ k ∈ s, X k) * X a)) * (two_half (m := m))
end Formalism.FourierDecayAlt.P.A6x6
