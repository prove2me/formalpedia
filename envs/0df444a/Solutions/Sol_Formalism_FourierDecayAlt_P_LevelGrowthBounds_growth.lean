-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LevelGrowthBounds.growth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:26.686468+00:00
-- url     : https://prove2.me/submissions/7f0a536e-6ff9-4e3e-a5b3-61c7f67aca9f

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_geom_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_Pp_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real
namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds
theorem _root_.solution (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (he : ∀ i, 0 ≤ e i) (ha : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ √(1 + e i) * ((1 + ε) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s))) :
    ∀ i, i ≤ r + 1 → a i ≤ (1 + (ε + 2 * δ)) ^ i * Pp e i * a 0 := by
  set ρ : ℝ := 1 + (ε + 2 * δ) with hρdef
  have hρ : (1:ℝ) ≤ ρ := by rw [hρdef]; linarith
  have hρ0 : (0:ℝ) ≤ ρ := by linarith
  have ha0 := ha 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ ρ ^ k * Pp e k * a 0 :=
        mul_nonneg (mul_nonneg (pow_nonneg hρ0 _) (Pp_nonneg he _)) ha0
      have hsum : ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s) ≤
          2 * δ * (ρ ^ k * Pp e k * a 0) := by
        calc ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)
            ≤ ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * (ρ ^ k * Pp e k * a 0) := by
              apply Finset.sum_le_sum
              intro s hs
              have hs' := Finset.mem_Icc.mp hs
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
              calc a (k+1-s) ≤ ρ ^ (k+1-s) * Pp e (k+1-s) * a 0 := ih _ (by omega) (by omega)
                _ ≤ ρ ^ k * Pp e k * a 0 := by
                  apply mul_le_mul_of_nonneg_right _ ha0
                  exact mul_le_mul (pow_le_pow_right₀ hρ (by omega)) (Pp_mono he (by omega))
                    (Pp_nonneg he _) (pow_nonneg hρ0 _)
          _ = (∑ s ∈ Icc 2 (k+1), δ ^ (s-1)) * (ρ ^ k * Pp e k * a 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * δ * (ρ ^ k * Pp e k * a 0) :=
              mul_le_mul_of_nonneg_right (geom_le δ hδ hδ2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : (0:ℝ) ≤ 1 + ε := by linarith
      calc a (k+1) ≤ √(1 + e (k+1)) * ((1 + ε) * a k +
            ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)) := h1
        _ ≤ √(1 + e (k+1)) * ((1 + ε) * (ρ ^ k * Pp e k * a 0) +
            2 * δ * (ρ ^ k * Pp e k * a 0)) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum) hs1
        _ = ρ ^ (k+1) * Pp e (k+1) * a 0 := by rw [Pp_succ, pow_succ, hρdef]; ring
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
