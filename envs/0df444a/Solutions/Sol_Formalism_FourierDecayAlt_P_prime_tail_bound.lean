-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.prime_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:28.744964+00:00
-- url     : https://prove2.me/submissions/1300a85a-779d-4113-8e3c-80c59ea4c78d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.PrimeTail := by
  intro s N hs
  have key : ∀ N : ℕ, 2 ≤ N → ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - 1 / N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have : (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have key2 : ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ ≤ 3 / 4 := by
    rcases lt_or_ge N 2 with h | h
    · rw [Finset.Icc_eq_empty (by omega)]; norm_num
    · have := key N h
      have : (0 : ℝ) ≤ 1 / N := by positivity
      linarith
  obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
  have h1 : ∀ l ∈ Icc 2 N, ((l : ℝ) ^ (2 + t))⁻¹ ≤ ((l : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ t)⁻¹ := by
    intro l hl
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Icc.1 hl).1
    rw [pow_add, mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hl2 t)
  calc _ ≤ ∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹ * ((2 : ℝ) ^ t)⁻¹ := Finset.sum_le_sum h1
    _ = (∑ l ∈ Icc 2 N, ((l : ℝ) ^ 2)⁻¹) * ((2 : ℝ) ^ t)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ 3 / 4 * ((2 : ℝ) ^ t)⁻¹ := mul_le_mul_of_nonneg_right key2 (by positivity)
    _ = _ := by rw [pow_add, mul_inv]; ring
end Formalism.FourierDecayAlt.P
