-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.growth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:47.129148+00:00
-- url     : https://prove2.me/submissions/636bae08-9534-4504-97d0-f4ce96f9fe02

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_geom_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_Pp_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ) (ρ : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hε : 0 ≤ ε) (he : ∀ i, 0 ≤ e i) (hσ : ∀ i, 0 ≤ σ i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t))
    (hρ1 : 1 + ε + 2 * a ≤ ρ) :
    ∀ i, i ≤ r + 1 → σ i ≤ Pp e i * ρ ^ i * σ 0 := by
  have hρ : (1:ℝ) ≤ ρ := by linarith
  have hσ0 := hσ 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ Pp e (k+1) * ρ ^ k * σ 0 :=
        mul_nonneg (mul_nonneg (Pp_nonneg he _) (pow_nonneg (by linarith) _)) hσ0
      have hsum : ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) ≤
          2 * a * (Pp e (k+1) * ρ ^ k * σ 0) := by
        calc ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t)
            ≤ ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              apply Finset.sum_le_sum
              intro t ht
              have ht' := Finset.mem_Icc.mp ht
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha _)
              calc σ (k+1-t) ≤ Pp e (k+1-t) * ρ ^ (k+1-t) * σ 0 := ih _ (by omega) (by omega)
                _ ≤ Pp e (k+1) * ρ ^ k * σ 0 := by
                  apply mul_le_mul_of_nonneg_right _ hσ0
                  exact mul_le_mul (Pp_mono he (by omega)) (pow_le_pow_right₀ hρ (by omega))
                    (pow_nonneg (by linarith) _) (Pp_nonneg he _)
          _ = (∑ t ∈ Icc 2 (k+1), a ^ (t-1)) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
              mul_le_mul_of_nonneg_right (geom_le a ha ha2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : 0 ≤ (1 + ε) * √(1 + e (k+1)) := mul_nonneg (by linarith) hs1
      calc σ (k+1) ≤ (1 + ε) * √(1 + e (k+1)) * σ k +
            ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) := h1
        _ ≤ (1 + ε) * √(1 + e (k+1)) * (Pp e k * ρ ^ k * σ 0) +
            2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
            add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum
        _ = (1 + ε + 2 * a) * (Pp e (k+1) * ρ ^ k * σ 0) := by rw [Pp_succ]; ring
        _ ≤ ρ * (Pp e (k+1) * ρ ^ k * σ 0) := mul_le_mul_of_nonneg_right hρ1 hB
        _ = Pp e (k+1) * ρ ^ (k+1) * σ 0 := by rw [pow_succ]; ring
end Formalism.FourierDecayAlt.P.Rec
