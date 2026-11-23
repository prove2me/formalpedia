-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:29.891804+00:00
-- url     : https://prove2.me/submissions/e0a34d75-c78c-4fa3-9cfe-ddec3cbd9d8e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_iteratedFDeriv_vanishing_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Sym
theorem _root_.solution {f : E → F} {r σ M : ℝ} (p : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hp : p ≤ N)
    (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) p N (M * (r + 1) ^ N) f := by
  refine ⟨hf, fun x hx i hi => ?_⟩
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx 0 (Nat.zero_le _))
  have hwpos : 0 < wt σ x := by unfold wt; positivity
  have hwle : wt σ x ≤ r + 1 := by unfold wt; linarith
  have hr1 : (1 : ℝ) ≤ r + 1 := by linarith
  rcases lt_or_ge i p with hip | hip
  · have h := iteratedFDeriv_vanishing_bound p hp hf hM h0 (p - i) (Nat.sub_le _ _) x hx
    have e1 : p - (p - i) = i := by omega
    rw [e1] at h
    have e2 : wt σ x ^ ((p : ℤ) - (i : ℤ)) = wt σ x ^ (p - i) := by
      rw [← zpow_natCast]
      congr 1
      push_cast [hip.le]
      ring
    rw [e2]
    calc ‖iteratedFDeriv ℝ i f x‖ ≤ M * ‖x‖ ^ (p - i) := h
      _ ≤ M * wt σ x ^ (p - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) (by unfold wt; linarith) _) hM0
      _ = M * 1 * wt σ x ^ (p - i) := by ring
      _ ≤ M * (r + 1) ^ N * wt σ x ^ (p - i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_pow₀ hr1) hM0)
            (pow_pos hwpos _).le
  · have e2 : wt σ x ^ ((p : ℤ) - (i : ℤ)) = (wt σ x ^ (i - p))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast [hip]
      ring
    rw [e2]
    have h1 : wt σ x ^ (i - p) ≤ (r + 1) ^ N :=
      (pow_le_pow_left₀ hwpos.le hwle _).trans (pow_le_pow_right₀ hr1 ((Nat.sub_le _ _).trans hi))
    have h2 : 1 ≤ (r + 1) ^ N * (wt σ x ^ (i - p))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hwpos _), one_mul]
      exact h1
    calc ‖iteratedFDeriv ℝ i f x‖ ≤ M := hM x hx i hi
      _ = M * 1 := by ring
      _ ≤ M * ((r + 1) ^ N * (wt σ x ^ (i - p))⁻¹) := mul_le_mul_of_nonneg_left h2 hM0
      _ = M * (r + 1) ^ N * (wt σ x ^ (i - p))⁻¹ := by ring
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
