-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.factorial_succ_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:10.286822+00:00
-- url     : https://prove2.me/submissions/a260b597-c163-43cb-bb61-1d1d10a5994e

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
theorem _root_.solution (g : PowerSeries K) (n : ℕ) :
    ((n + 1).factorial : K) * PowerSeries.coeff (n + 1) g =
      (n.factorial : K) * PowerSeries.coeff n (PowerSeries.derivative K g) := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring
end Formalism.L2.Th1.C.JetSubstitutionLemmas
