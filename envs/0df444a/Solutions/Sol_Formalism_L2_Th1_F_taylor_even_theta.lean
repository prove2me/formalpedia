-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylor_even_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:46.466881+00:00
-- url     : https://prove2.me/submissions/06fae7ac-d8fc-4c40-80c4-e6aa137ea86c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_sigS_add_const
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_v_zero
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_analyticAt_v
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_ode_th
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_ode_v
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_pExcept
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_analyticAt_v
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_constantCoeff_taylor0
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_formal_unique
import Theorems.Thm_Formalism_L2_Th1_F_TaylorSigmaUniqueness_ode_v
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_const
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_id
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_congr
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_deriv
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_mul
import Theorems.Thm_Formalism_L2_Th1_F_taylor_ring
import Theorems.Thm_Formalism_L2_Th1_F_th0Basic


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
open ThetaZeroTaylorLemmas TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution : TaylorTh0 := by
  intro L ω₀ hω ht
  have hr := taylor_ring
  set t := ω₀ / 2 with htdef
  have h2t : 2 * t ∈ L.lattice := by
    have : 2 * t = ω₀ := by rw [htdef]; ring
    rwa [this]
  set e := L.weierstrassP t with he
  set κ := 3 * e ^ 2 - L.g₂ / 4 with hκ
  obtain ⟨hdiff, h0, -⟩ := th0Basic L ω₀ hω ht
  have hθ : AnalyticAt ℂ (th0 L t) 0 := hdiff.analyticAt 0
  have hv : AnalyticAt ℂ (v L t) 0 := analyticAt_v L ht
  have eU : PowerSeries.derivative ℂ (taylor0 (th0 L t)) = taylor0 (v L t) * taylor0 (th0 L t) := by
    rw [← Taylor.taylor0_deriv, ← Taylor.taylor0_mul hv hθ]
    exact Taylor.taylor0_congr (ode_th L hω ht)
  have Tid := T.id hr
  have Tzz := T.mul hr Tid Tid
  have Tp : T (L.weierstrassPExcept 0) (pSeries L) := ⟨TaylorSigmaUniqueness.analyticAt_pExcept L, rfl⟩
  have Tdv : T (deriv (v L t)) (PowerSeries.derivative ℂ (taylor0 (v L t))) :=
    ⟨hv.deriv, Taylor.taylor0_deriv _⟩
  have TL := T.mul hr (T.add hr (T.add hr (T.const hr 1) (T.mul hr Tzz Tp)) (T.mul hr (T.const hr (-e)) Tzz))
    (T.add hr (T.add hr Tdv (T.const hr e)) (T.const hr (s2 L)))
  have TR := T.mul hr (T.const hr (-κ)) Tzz
  have hE := TL.2.symm.trans ((Taylor.taylor0_congr (ode_v L ht h2t)).trans TR.2)
  rw [map_one, map_neg, map_neg] at hE
  set V := taylor0 (v L t) with hV
  set P := pSeries L with hP
  have hD0 : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e * PowerSeries.X ^ 2 : PowerSeries ℂ) ≠ 0 := by
    simp
  have hD := PowerSeries.mul_inv_cancel _ hD0
  have eV : PowerSeries.derivative ℂ V
      = -(PowerSeries.C e + PowerSeries.C κ * B.wOf e P + PowerSeries.C (s2 L)) := by
    rw [B.wOf]
    generalize (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e * PowerSeries.X ^ 2 : PowerSeries ℂ)⁻¹ = Di
      at hD ⊢
    linear_combination Di * hE
      - (PowerSeries.derivative ℂ V + PowerSeries.C e + PowerSeries.C (s2 L)) * hD
  have key := TaylorSigmaUniqueness.formal_unique
    (PowerSeries.C e + PowerSeries.C κ * B.wOf e P + PowerSeries.C (s2 L)) (taylor0 (th0 L t)) V
    (by rw [eV, mul_neg]) (by rw [TaylorSigmaUniqueness.constantCoeff_taylor0, v_zero])
    (by rw [eU]) (by rw [TaylorSigmaUniqueness.constantCoeff_taylor0, h0])
  rw [key, sigS_add_const, B.sigma1, B.sigmaOneSeries]
  refine B.fExp_add ?_ ?_
  · have : PowerSeries.constantCoeff
        (-B.prim (B.prim (PowerSeries.C e + PowerSeries.C κ * B.wOf e P)) : PowerSeries ℂ) = 0 := by
      rw [map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  · have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this
end Formalism.L2.Th1.F
