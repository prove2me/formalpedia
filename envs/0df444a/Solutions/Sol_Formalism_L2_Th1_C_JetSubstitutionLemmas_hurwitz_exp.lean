-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:33.616051+00:00
-- url     : https://prove2.me/submissions/80119733-10bc-486a-8818-2a06dcacdc31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hurwitz_mul
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_factorial_succ_coeff
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_derivative_mvExp


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K] {R : Subring K}
variable [CharZero K]
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {F : PowerSeries K} (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : ∀ i : ℕ, 1 ≤ i → (i.factorial : K) * PowerSeries.coeff i F ∈ R) (n : ℕ) :
    (n.factorial : K) * PowerSeries.coeff n (mvExp F : PowerSeries K) ∈ R := by
  have hE' := derivative_mvExp (K := K) hF0
  have hE0 : PowerSeries.constantCoeff (mvExp F : PowerSeries K) = 1 := IntegralMvPolynomialLemmas.constantCoeff_mvExp hF0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0, one_mem]
    | succ n =>
      rw [factorial_succ_coeff, hE']
      refine hurwitz_mul n (fun j hj => ?_) (fun k hk => ih k (by omega))
      rw [← factorial_succ_coeff]
      exact hF (j + 1) (by omega)
end Formalism.L2.Th1.C.JetSubstitutionLemmas
