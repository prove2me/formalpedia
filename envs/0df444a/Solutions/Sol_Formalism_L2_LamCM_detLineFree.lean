-- Prove2me | solution 1 for Formalism.L2.LamCM.detLineFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:21.928469+00:00
-- url     : https://prove2.me/submissions/dab567c7-d5d5-4221-bd74-f49db4d9d88a

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_absNorm_span_real
import Theorems.Thm_Formalism_L2_LamCM_A2_det_re_pos
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_A2_deg_detLine
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_free
import Theorems.Thm_Formalism_L2_LamCM_A2_gramC_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open A2
namespace Formalism.L2.LamCM
theorem _root_.solution : DetFree := by
  intro K _ _ m L b hL hb
  have hI := detIdeal_free L b hL hb
  have hne : (Matrix.of b).det ≠ 0 := by
    intro h
    apply detIdeal_ne_zero L hL
    rw [hI, h, FractionalIdeal.spanSingleton_zero]
  have hσ : ∀ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re =
      2 * Real.log ‖σ (Matrix.of b).det‖ + 2 * Real.log (Real.sqrt (L.H σ).det.re) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hn : 0 < ‖σ (Matrix.of b).det‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hne)
    rw [gramC_det, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, Real.log_mul (by positivity) hD.ne',
      Real.log_pow, Real.log_sqrt hD.le]
    push_cast
    ring
  rw [deg_detLine, hI, absNorm_span_real,
    Real.log_prod (fun σ _ => (norm_pos_iff.2 ((map_ne_zero σ).2 hne)).ne')]
  simp_rw [hσ, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end Formalism.L2.LamCM
