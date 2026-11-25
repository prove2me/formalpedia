-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:26.325528+00:00
-- url     : https://prove2.me/submissions/78aecb12-d103-4b21-9af9-09bfa73177c2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hsM
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst_zero
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_subst_subst_l

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
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {w : MvPowerSeries σ K} (hw : MvPowerSeries.constantCoeff w = 0) :
    PowerSeries.subst w ph =
      PowerSeries.subst (PowerSeries.subst w l) (PowerSeries.subst linv ph) := by
  rw [PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM (cc_subst_zero hw h.1)), subst_subst_l h hw]
end Formalism.L2.Th1.C.JetSubstitutionLemmas
