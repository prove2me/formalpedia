-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.hurwitz_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:12.517545+00:00
-- url     : https://prove2.me/submissions/98a85fb1-53d6-4fa7-b1ff-57073695fe2f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG

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
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {A B : PowerSeries K} (n : ℕ)
    (hA : ∀ j ≤ n, (j.factorial : K) * PowerSeries.coeff j A ∈ R)
    (hB : ∀ k ≤ n, (k.factorial : K) * PowerSeries.coeff k B ∈ R) :
    (n.factorial : K) * PowerSeries.coeff n (A * B) ∈ R := by
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have e : (n.factorial : K) * (PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B) =
      ((n.choose p.1 : ℕ) : K) * ((p.1.factorial : K) * PowerSeries.coeff p.1 A) *
        ((p.2.factorial : K) * PowerSeries.coeff p.2 B) := by
    rw [← hp', ← Nat.add_choose_mul_factorial_mul_factorial p.1 p.2]
    push_cast
    rw [Nat.choose_symm_add]
    ring
  rw [e]
  exact mul_mem (mul_mem (natCast_mem R _) (hA _ (by omega))) (hB _ (by omega))
end Formalism.L2.Th1.C.JetSubstitutionLemmas
