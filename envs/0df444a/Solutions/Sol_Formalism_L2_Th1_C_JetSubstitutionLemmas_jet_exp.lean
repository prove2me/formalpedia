-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.jet_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:41.617474+00:00
-- url     : https://prove2.me/submissions/12d588dc-8cde-456b-9c52-e207c6831d32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_eq
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hurwitz_exp

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
theorem _root_.solution {l linv F : PowerSeries K} (h : IsLogPair l linv)
    (hF0 : PowerSeries.constantCoeff F = 0) (hF : ∀ i : ℕ, 1 ≤ i → jet l F i ∈ R) (i : ℕ) :
    jet l (mvExp F : PowerSeries K) i ∈ R := by
  have hi := hs1 h.2.2.1
  have hF0' : PowerSeries.constantCoeff (PowerSeries.subst linv F : PowerSeries K) = 0 := by
    rw [cc_subst1 h.2.2.1]
    exact hF0
  have e : PowerSeries.subst linv (mvExp F : PowerSeries K) =
      (mvExp (PowerSeries.subst linv F : PowerSeries K) : PowerSeries K) := by
    unfold mvExp
    exact PowerSeries.subst_comp_subst_apply (hs1 hF0) hi _
  rw [jet_eq h, e]
  exact hurwitz_exp hF0' (fun j hj => by rw [← jet_eq h]; exact hF j hj) i
end Formalism.L2.Th1.C.JetSubstitutionLemmas
