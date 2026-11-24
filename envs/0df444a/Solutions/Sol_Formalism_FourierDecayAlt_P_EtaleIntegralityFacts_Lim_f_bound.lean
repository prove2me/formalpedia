-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.f_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:03.362801+00:00
-- url     : https://prove2.me/submissions/b73aca91-e2f3-440c-95ba-1bfef84bd596

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_y_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_norm_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_cutoff_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution (m : ℕ) (β : ℂ) (ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) {c K' : ℝ} (hc : 0 < c)
    (ht : t ≠ 0) (hK' : 0 ≤ K') (hcof : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε) → c / 2 ≤ ‖cofXY m t p‖)
    (hΦ : cofXY m t p ≠ 0 → ‖Φ (MXY m D t p)‖ ≤ K') :
    ‖ampIn β m ε Φ D t p‖ ≤ (2 / c) ^ 2 * K' := by
  have hT : 0 < ‖t‖ ^ (-ε) := Real.rpow_pos_of_pos (norm_pos_iff.mpr ht) _
  obtain ⟨hc0, hc1, -, hcz⟩ := (matrix_cutoff_spec (m + 1 + 1)).1 (‖t‖ ^ (-ε)) (MXY m D t p) hT
  by_cases hy : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε)
  · have hl := hcof hy
    have hne : cofXY m t p ≠ 0 := by
      rw [← norm_pos_iff]
      linarith
    rw [ampIn, amp, cutPhi, norm_smul, norm_smul, norm_mul, norm_psi, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0,
      abs_of_nonneg (by positivity)]
    have e1 : (‖cofXY m t p‖ ^ 2)⁻¹ ≤ (2 / c) ^ 2 := by
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hl
    have e2 : cutM (‖t‖ ^ (-ε)) (MXY m D t p) * ‖Φ (MXY m D t p)‖ ≤ K' := by
      calc cutM (‖t‖ ^ (-ε)) (MXY m D t p) * ‖Φ (MXY m D t p)‖ ≤ 1 * K' :=
            mul_le_mul hc1 (hΦ hne) (norm_nonneg _) zero_le_one
        _ = K' := one_mul _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · push Not at hy
    have h0 := hcz (hy.le.trans (y_le_MXY m D t p))
    rw [ampIn, amp, cutPhi, h0]
    simp only [Complex.ofReal_zero, zero_smul, smul_zero, norm_zero]
    positivity
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
