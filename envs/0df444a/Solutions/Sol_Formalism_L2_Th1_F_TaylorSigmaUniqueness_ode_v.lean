-- Prove2me | solution 1 for Formalism.L2.Th1.F.TaylorSigmaUniqueness.ode_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:16.895951+00:00
-- url     : https://prove2.me/submissions/c7df42d8-6856-4d92-ba7a-bda3be4d7ede

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_zetaExcept_zero_add
import Theorems.Thm_Formalism_L2_Th1_F_zeta_has_deriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.TaylorSigmaUniqueness
namespace Formalism.L2.Th1.F.TaylorSigmaUniqueness
theorem _root_.solution (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -(z * L.weierstrassPExcept 0 z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := zeta_has_deriv L z hzl
  have h2 : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z := by
    simpa only [one_div] using hasDerivAt_inv h0
  have h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w := by
    funext w
    rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]
    ring
  have h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2) :=
    (h1.sub h2).deriv
  rw [h3, h4]
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  rw [← h5]
  ring
end Formalism.L2.Th1.F.TaylorSigmaUniqueness
