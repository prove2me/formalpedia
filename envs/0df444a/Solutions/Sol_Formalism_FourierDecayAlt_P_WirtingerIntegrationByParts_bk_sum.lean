-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:12.30847+00:00
-- url     : https://prove2.me/submissions/92afb7fa-e2d2-4d55-a8ab-3c903dea9bd3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_N_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} (hne : fderiv ℂ g x ≠ 0) :
    ∑ k, fderiv ℂ g x (Pi.single k 1) * bk g k x = 1 := by
  have hN := bkb_N_pos hne
  unfold bk
  have : ∀ k, fderiv ℂ g x (Pi.single k 1) *
      ((∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ • (starRingEnd ℂ) (fderiv ℂ g x (Pi.single k 1))) =
      ((∑ l, Complex.normSq (fderiv ℂ g x (Pi.single l 1)))⁻¹ : ℝ) *
        ((Complex.normSq (fderiv ℂ g x (Pi.single k 1)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.real_smul, Complex.normSq_eq_conj_mul_self]; ring
  simp only [this]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne']
  simp
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
