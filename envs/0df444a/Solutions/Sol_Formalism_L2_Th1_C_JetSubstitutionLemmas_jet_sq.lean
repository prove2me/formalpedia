-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.jet_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:26.654825+00:00
-- url     : https://prove2.me/submissions/bcc84200-1d45-4d3d-b28d-835cacc9eb2f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_eq

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
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (c : K) (i : ℕ) :
    jet l (PowerSeries.C c * l ^ 2) i = if i = 2 then 2 * c else 0 := by
  have hi := hs1 h.2.2.1
  rw [jet_eq h]
  have e : PowerSeries.subst linv (PowerSeries.C c * l ^ 2) = PowerSeries.C c * PowerSeries.X ^ 2 := by
    rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hi, ← PowerSeries.coe_substAlgHom hi, map_pow,
      PowerSeries.coe_substAlgHom hi, h.2.2.2.2, PowerSeries.smul_eq_C_mul]
  rw [e, PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h2
  · subst h2
    norm_num [Nat.factorial]
  · simp
end Formalism.L2.Th1.C.JetSubstitutionLemmas
