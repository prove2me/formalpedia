-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylorSigma_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:14.848427+00:00
-- url     : https://prove2.me/submissions/3f5e48fd-8ff3-49a0-9208-5646e13d73e1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_formal_unique
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_constantCoeff_taylor0
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_differentiable_u
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_u_zero
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_v
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_pExcept
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_ode_u
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_ode_v
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_zetaExcept_zero_zero


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
open TaylorSigmaUniqueness
namespace Formalism.L2.Th1.F
theorem _root_.solution (hr : TaylorRing) (hd : TaylorDeriv) : TaylorSigma := by
  intro L
  obtain ⟨hadd, hC, hX, hgerm⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hu : AnalyticAt ℂ (u L) 0 := (differentiable_u L).analyticAt 0
  have hv := analyticAt_v L
  have hp := analyticAt_pExcept L
  have e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L) := by
    have := (hadd (fun z => z) (u L) hid hu).2
    rw [hX] at this
    exact this
  have eU : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (u L))
      = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L)) := by
    have hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0 := hv.mul hu
    rw [← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2,
      ← (hadd _ _ hid hvu).2]
    exact hgerm _ _ (ode_u L)
  have eV : PowerSeries.X * PowerSeries.derivative ℂ (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0))
      = -(PowerSeries.X * pSeries L) := by
    have hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z))
        = -(PowerSeries.X * pSeries L) := by
      have hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0 := hid.mul hp
      rw [(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC,
        (hadd _ _ hid hp).2, hX, pSeries]
      simp
    rw [← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]
    refine hgerm _ _ ((ode_v L).mono fun z hz => ?_)
    show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)
    rw [hz]; ring
  rw [e1, B.sigma]
  congr 1
  refine formal_unique (pSeries L) _ _ eV ?_ eU ?_
  · rw [constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]
  · rw [constantCoeff_taylor0, u_zero]
end Formalism.L2.Th1.F
