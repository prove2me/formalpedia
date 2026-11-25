-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.key_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:13.621487+00:00
-- url     : https://prove2.me/submissions/ee479296-755c-4999-b780-11a1dd2f0c7b

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_mul_normSq_tp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_schur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {N : (Fin d → ℝ) → ℝ} {A : (Fin d → ℤ) → ℂ} (hint : Integrable N)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re)
    (hsum : Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖))
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z, N z * ‖tp B c z‖ ^ 2 ≤
      (∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) * ∑ σ ∈ B, ‖c σ‖ ^ 2 := by
  have h1 := integral_mul_normSq_tp hint B c
  have h2 := hPD B c
  have h3 : (∑ σ ∈ B, ∑ σ' ∈ B,
      ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')) =
      ((∫ z, N z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) +
        ∑ σ ∈ B, ∑ σ' ∈ B, A (σ - σ') * c σ * starRingEnd ℂ (c σ') := by
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    ring
  have h4 : ∫ z, N z * ‖tp B c z‖ ^ 2 ≤ (∑ σ ∈ B, ∑ σ' ∈ B,
      ((∫ z, (N z : ℂ) * ee z (σ - σ')) + A (σ - σ')) * c σ * starRingEnd ℂ (c σ')).re := by
    rw [h3, Complex.add_re, Complex.ofReal_re]
    linarith
  refine h4.trans ((Complex.re_le_norm _).trans ?_)
  refine le_trans ?_ (schur (fun σ => norm_nonneg _) hsum B (fun σ => ‖c σ‖))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ' _ => ?_))
  rw [norm_mul, norm_mul, RCLike.norm_conj]
end Formalism.FourierDecayAlt.P.HLsc
