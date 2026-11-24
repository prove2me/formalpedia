-- Prove2me | solution 1 for Formalism.L2.Th1.C.binom_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:10.086558+00:00
-- url     : https://prove2.me/submissions/eaaad9fa-7bc4-475e-bddc-d67cd141a3e8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution (z : K) (n : ℕ) : ((n : K) + 1) * binom z (n + 1) = (z - n) * binom z n := by
  unfold binom
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  have h0 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h1 : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
end Formalism.L2.Th1.C
