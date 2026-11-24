-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_linv_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:40.912928+00:00
-- url     : https://prove2.me/submissions/d55b9f03-bbd7-411f-9daa-c4bd0c0d92da

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_mulBy

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
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K)
    (ph : PowerSeries K) :
    PowerSeries.subst linv (PowerSeries.subst (mulBy l linv a) ph) =
      PowerSeries.rescale a (PowerSeries.subst linv ph) := by
  have hi := hs1 h.2.2.1
  have hm : PowerSeries.HasSubst (mulBy l linv a) := hs1 (cc_mulBy h a)
  have haX : PowerSeries.HasSubst (a • PowerSeries.X : PowerSeries K) := hs1 (by simp)
  have hCl : PowerSeries.HasSubst (PowerSeries.C a * l) := hs1 (by simp [h.1])
  rw [PowerSeries.subst_comp_subst_apply hm hi, PowerSeries.rescale_eq_subst]
  have e1 : PowerSeries.subst linv (mulBy l linv a) = PowerSeries.subst (a • PowerSeries.X : PowerSeries K) linv := by
    unfold mulBy
    rw [PowerSeries.subst_comp_subst_apply hCl hi]
    congr 1
    rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hi, h.2.2.2.2]
  rw [e1]
  exact (PowerSeries.subst_comp_subst_apply hi haX ph).symm
end Formalism.L2.Th1.C.JetSubstitutionLemmas
