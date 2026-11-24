-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThetaZeroTaylorLemmas.sigS_add_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:46:08.069731+00:00
-- url     : https://prove2.me/submissions/0eae45fa-e64f-418e-b27c-fb8a6384e5e6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorEvenTheta
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroTaylorLemmas_derivative_prim
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim


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
open Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
open PowerSeries
namespace Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
theorem _root_.solution (Q : PowerSeries ℂ) (s : ℂ) :
    B.sigS (Q + C s) = -B.prim (B.prim Q) + -(C (s / 2) * X ^ 2) := by
  have h1 : derivative ℂ (C (s / 2) * X ^ 2 : PowerSeries ℂ) = C s * X := by
    have hs : (C s : PowerSeries ℂ) = C (s / 2) * 2 := by
      rw [show (2 : PowerSeries ℂ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
      congr 1
      ring
    rw [Derivation.leibniz, derivative_C, Derivation.leibniz_pow, derivative_X, hs]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero, mul_one, Nat.cast_ofNat]
    ring
  have h2 : derivative ℂ (C s * X : PowerSeries ℂ) = C s := by
    rw [Derivation.leibniz, derivative_C, derivative_X]
    simp
  refine derivative.ext (derivative.ext ?_ ?_) ?_
  · rw [B.sigS, map_neg, map_neg, derivative_prim, derivative_prim, map_add, map_add, map_neg,
      map_neg, map_neg, map_neg, derivative_prim, derivative_prim, h1, h2, neg_add]
  · rw [B.sigS, map_neg, map_neg, derivative_prim, map_add, map_neg, map_neg, derivative_prim, h1]
    simp [B.constantCoeff_prim]
  · simp [B.sigS, B.constantCoeff_prim]
end Formalism.L2.Th1.F.ThetaZeroTaylorLemmas
