-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.cvec_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:37.001728+00:00
-- url     : https://prove2.me/submissions/b9aa0bd1-c2b8-4472-80f7-e76df612375c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integral_comp_mul_C


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (F G : ℂ → ℂ → H) (x x' : ℂ) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ =
      ∫ D, ⟪F x D, ((‖x ^ (s - 1) / x' ^ (s - 1)‖ : ℝ) : ℂ) • G x' ((x ^ (s - 1) / x' ^ (s - 1)) * D)⟫_ℂ := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx0' : ‖x'‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hk : ‖x ^ (s - 1)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have key := integral_comp_mul_C (fun c => ⟪cvec s F x c, cvec s G x' c⟫_ℂ) (x ^ (s - 1)) ha
  have hL : ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ
      = (‖x ^ (s - 1)‖ ^ 2) • ∫ z, ⟪cvec s F x (x ^ (s - 1) * z), cvec s G x' (x ^ (s - 1) * z)⟫_ℂ := by
    rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  rw [hL, ← integral_smul]
  congr 1
  funext D
  simp only [cvec]
  rw [mul_div_cancel_left₀ D ha, mul_div_right_comm (x ^ (s - 1)) D (x' ^ (s - 1))]
  have hc : ‖x ^ (s - 1)‖ ^ 2 * (‖x‖ ^ (s - 1))⁻¹ * (‖x'‖ ^ (s - 1))⁻¹
      = ‖x ^ (s - 1) / x' ^ (s - 1)‖ := by
    rw [norm_div, norm_pow, norm_pow]
    field_simp
  rw [inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal, Complex.real_smul, ← hc]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.PBK
