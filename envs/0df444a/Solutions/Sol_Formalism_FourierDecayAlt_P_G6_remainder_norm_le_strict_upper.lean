-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G6.remainder_norm_le_strict_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:59:19.574741+00:00
-- url     : https://prove2.me/submissions/b3da7ccc-ae75-4813-9a8a-3e91946fd661

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_mulVec_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_norm_pow_mulVec_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G6
theorem _root_.solution {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {ρ' : Fin m → ℂ} {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hS : IsStrictUpper X)
    (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (hρ : ∀ k, ‖ρ' k‖ ≤ L) :
    ‖R0 X B ρ' t‖ ≤ (((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m)) * (L ^ (m + 2) * ‖t‖) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have term : ∀ j ∈ Finset.range (m + 1),
      ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ ≤
        ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hjm : j = m
    · subst hjm
      rw [Finset.sum_eq_zero, zero_mul, norm_zero]
      · positivity
      · intro k _
        rw [pow_mulVec_succ (isStrictUpper_neg hS), mul_zero]
    · have hlt : j < m := by omega
      rw [norm_mul, norm_pow]
      have h1 : ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ ≤
          (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by
        calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖
            ≤ ∑ k : Fin m, ‖ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin m, L * (((m : ℝ) + 1) ^ j * L ^ (j + 1)) := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [norm_mul]
              exact mul_le_mul (hρ k) (norm_pow_mulVec_le hL0 hX hB j k.succ) (norm_nonneg _) hL0
          _ = (m : ℝ) * (((m : ℝ) + 1) ^ j * L ^ (j + 2)) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
          _ ≤ (m : ℝ) * (((m : ℝ) + 1) ^ m * L ^ (m + 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
              refine mul_le_mul (pow_le_pow_right₀ hm1 hlt.le) (pow_le_pow_right₀ hL (by omega))
                (by positivity) (by positivity)
          _ = (m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2) := by ring
      have h2 : ‖t‖ ^ (m - j) ≤ ‖t‖ := pow_le_of_le_one (norm_nonneg _) ht (by omega)
      calc ‖∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ‖ * ‖t‖ ^ (m - j)
          ≤ ((m : ℝ) * ((m : ℝ) + 1) ^ m * L ^ (m + 2)) * ‖t‖ :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
  calc ‖R0 X B ρ' t‖ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖(∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ) * t ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 2) * ‖t‖) :=
        Finset.sum_le_sum term
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
end Formalism.FourierDecayAlt.P.G6
