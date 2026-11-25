-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.memLp_cvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:46.913241+00:00
-- url     : https://prove2.me/submissions/252c9b01-4b17-4f7f-9673-12dd6e4b235f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_cvec_eq_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_comp_mul


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
theorem _root_.solution (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    MemLp (F x) 2 volume ↔ MemLp (cvec s F x) 2 volume := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [cvec_eq_comp]
    exact (memLp_comp_mul h _ (inv_ne_zero ha)).const_smul _
  · have := (memLp_comp_mul h (x ^ (s - 1)) ha).const_smul ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
    convert this using 1
    funext D
    simp only [Pi.smul_apply, cvec, smul_smul]
    rw [mul_div_cancel_left₀ D ha, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]
end Formalism.FourierDecayAlt.P.PBK
