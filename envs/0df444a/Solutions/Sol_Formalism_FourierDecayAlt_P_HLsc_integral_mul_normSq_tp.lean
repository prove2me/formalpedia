-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integral_mul_normSq_tp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:33.096731+00:00
-- url     : https://prove2.me/submissions/698915f6-d544-427f-80cd-279028f919e7

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_normSq_tp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integrable_mul_ee

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
theorem _root_.solution {W : (Fin d → ℝ) → ℝ} (hW : Integrable W)
    (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ((∫ z, W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, (∫ z, (W z : ℂ) * ee z (σ - σ')) * c σ * starRingEnd ℂ (c σ') := by
  rw [← integral_complex_ofReal]
  have h1 : ∀ z, ((W z * ‖tp B c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, ((W z : ℂ) * ee z (σ - σ')) * (c σ * starRingEnd ℂ (c σ')) := by
    intro z
    rw [Complex.ofReal_mul, normSq_tp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ' _ => ?_)
    ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun σ' _ => ?_)
      rw [integral_mul_const, mul_assoc]
    · intro σ' _
      exact (integrable_mul_ee hW _).mul_const _
  · intro σ _
    exact integrable_finsetSum _ (fun σ' _ => (integrable_mul_ee hW _).mul_const _)
end Formalism.FourierDecayAlt.P.HLsc
