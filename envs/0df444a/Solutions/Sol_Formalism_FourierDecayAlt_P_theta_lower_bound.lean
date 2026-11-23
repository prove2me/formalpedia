-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theta_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:09.675314+00:00
-- url     : https://prove2.me/submissions/06486237-c2c2-4952-af47-a5aeb1ce174c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz8_cmRing_idempotent_unitRatio_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ThetaLower := by
  intro f k C A0 Ct N I Del TT Th hf hk hC hA0 hCt hN hI hDel hTT hTh hCN h
  have hk0 : (0:ℝ) < k := by have : (1:ℝ) ≤ k := by exact_mod_cast hk
                             linarith
  have hC0 : 0 < C := by linarith
  have hCt0 : 0 < Ct := by linarith
  have hinv : ∀ X : ℝ, 0 < X → Th⁻¹ ≤ X → X⁻¹ ≤ Th := fun X hX hX' => by
    have := inv_anti₀ (inv_pos.mpr hTh) hX'; rwa [inv_inv] at this
  have hq0 : 0 < C * Real.pi * N / I := by positivity
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hs0 : 0 < Real.sqrt (k * N ^ 3 / Del) := Real.sqrt_pos.mpr (by positivity)
  have hsT : 0 < Real.sqrt TT := Real.sqrt_pos.mpr hTT
  have hmin1 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0) := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin3 : min (min (Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0))
        (I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N)))
      (Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k))) ≤
      Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)) := min_le_right _ _
  have c23 : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) →
      I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) ≤ Th := fun h' => by
    have e : I / (Real.pi * Ct * C ^ 2 * A0 * Real.sqrt k * N) =
        (Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)))⁻¹ := by
      field_simp; try ring
    rw [e]; exact hinv _ (by positivity) h'
  rcases h with h | h | h | h
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt (k * N ^ 3 / Del)) Th hCt (by positivity) hTh
      (by rw [mul_pow, ← mul_assoc]; exact h)
    have e : Real.sqrt (Del / (k * N ^ 3)) / (Ct * C * A0) =
        (Ct * (C * A0 * Real.sqrt (k * N ^ 3 / Del)))⁻¹ := by
      rw [show Del / (k * N ^ 3) = (k * N ^ 3 / Del)⁻¹ from (inv_div _ _).symm, Real.sqrt_inv]
      field_simp
    exact le_trans hmin1 (by rw [e]; exact hinv _ (by positivity) h')
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I) ^ 2) Th hCt
      (by positivity) hTh (by rw [mul_pow, ← pow_mul, ← mul_assoc]; exact h)
    have hq2 : (C * Real.pi * N / I) ^ 2 ≤ C * Real.pi * N / I := by
      rw [sq]; exact mul_le_of_le_one_left hq0.le hCN
    have h'' : Th⁻¹ ≤ Ct * (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) := by
      refine le_trans h' (mul_le_mul_of_nonneg_left ?_ hCt0.le)
      exact mul_le_mul_of_nonneg_left hq2 (by positivity)
    exact le_trans hmin2 (c23 h'')
  · have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf Ct (C * A0 * Real.sqrt k * (C * Real.pi * N / I)) Th hCt
      (by positivity) hTh (by rw [mul_pow, ← mul_assoc]; exact h)
    exact le_trans hmin2 (c23 h')
  · have hsCt : 1 ≤ Real.sqrt Ct := Real.one_le_sqrt.mpr hCt
    have h' := Sz8.cmRing_idempotent_unitRatio_identity f hf (Real.sqrt Ct) (Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT))
      Th hsCt (Real.sqrt_nonneg _) hTh h
    have e : Real.sqrt (Real.sqrt TT / (Real.pi * Ct * C * A0 * Real.sqrt k)) =
        (Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT))⁻¹ := by
      rw [← Real.sqrt_mul hCt0.le, ← Real.sqrt_inv]; congr 1; field_simp
    have hpos : 0 < Real.sqrt Ct * Real.sqrt (Real.pi * C * A0 * Real.sqrt k / Real.sqrt TT) := by
      apply mul_pos (Real.sqrt_pos.mpr hCt0) (Real.sqrt_pos.mpr (by positivity))
    exact le_trans hmin3 (by rw [e]; exact hinv _ hpos h')
end Formalism.FourierDecayAlt.P
