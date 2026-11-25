-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hessian_jet_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:21.00862+00:00
-- url     : https://prove2.me/submissions/ef62f0ac-e359-4b7f-914e-d3a57a8bd804

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_e_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_p_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_two_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_prod_jet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.HessianJet := by
  intro m d hd
  have key : ((∏ k : Fin m, (1 + MvPolynomial.X k)) *
      (1 - ∑ k : Fin m, MvPolynomial.X k + MvPolynomial.C (1 / 2 : ℚ) *
        (∑ k : Fin m, MvPolynomial.X k ^ 2 + (∑ k : Fin m, MvPolynomial.X k) ^ 2)) -
      1 : MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
    have hD := A6x6.prod_jet (m := m) Finset.univ
    have he := A6x6.e_mem (m := m) Finset.univ
    have hp := A6x6.p_mem (m := m) Finset.univ
    have he2 := Ideal.pow_mem_pow he 2
    have h1 : ((∑ k : Fin m, MvPolynomial.X k) * ∑ k : Fin m, MvPolynomial.X k ^ 2 :
        MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
      rw [pow_succ' _ 2]; exact Ideal.mul_mem_mul he hp
    have h2 : (((∑ k : Fin m, MvPolynomial.X k) ^ 2 - ∑ k : Fin m, MvPolynomial.X k ^ 2) *
        ((∑ k : Fin m, MvPolynomial.X k) ^ 2 + ∑ k : Fin m, MvPolynomial.X k ^ 2) :
        MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
      have : _ ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 2 * MvPolynomial.idealOfVars (Fin m) ℚ ^ 2 :=
        Ideal.mul_mem_mul (Ideal.sub_mem _ he2 hp) (Ideal.add_mem _ he2 hp)
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by norm_num) this
    have h3 := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right
      (1 - ∑ k : Fin m, MvPolynomial.X k + MvPolynomial.C (1 / 2 : ℚ) *
        (∑ k : Fin m, MvPolynomial.X k ^ 2 + (∑ k : Fin m, MvPolynomial.X k) ^ 2)) _ hD) h1)
      (Ideal.mul_mem_left _ (MvPolynomial.C (1 / 2 : ℚ) ^ 2) h2)
    convert h3 using 1
    linear_combination ((∑ k : Fin m, MvPolynomial.X k) ^ 2 +
      (∑ k : Fin m, MvPolynomial.X k) * ∑ k : Fin m, MvPolynomial.X k ^ 2) *
      (A6x6.two_half (m := m))
  exact (MvPolynomial.mem_pow_idealOfVars_iff 3 _).1 key d hd
end Formalism.FourierDecayAlt.P
