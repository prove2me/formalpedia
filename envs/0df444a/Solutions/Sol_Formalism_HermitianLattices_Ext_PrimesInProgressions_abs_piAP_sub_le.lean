-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.abs_piAP_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:32:33.340813+00:00
-- url     : https://prove2.me/submissions/c4b9dc3d-99ba-48b6-afc6-a2d99331a29d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_vonMangoldtAP_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_vonMangoldtAP_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(piAP X M b : ℝ) - ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * cAP M b n| ≤ 4 * √X * Real.log X := by
  have hpi : (piAP X M b : ℝ) = ∑ n ∈ Icc 0 ⌊X⌋₊, (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) := by
    unfold piAP
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn'
    have : n = 0 := by
      rw [Finset.mem_Icc] at hn hn'
      omega
    subst this
    simp [Nat.not_prime_zero]
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ n : ℕ, 0 ≤ (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ∧
      (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ≤
        2 * (if ¬ n.Prime then Λ n else 0) := by
    intro n
    by_cases hp : n.Prime
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      by_cases hm : n % M = b % M
      · have hm' : n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm', vonMangoldt_apply_prime hp, hlog]
      · have hm' : ¬ n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm']
    · simp only [hp, false_and, if_false, sub_zero, not_false_eq_true, if_true]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h0 : Λ n = 0 := by
          interval_cases n <;> simp
        have h0' : cAP M b n = 0 := le_antisymm (h0 ▸ vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n)
        simp [h0, h0']
      · have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        have hpos : 0 < Real.log n := by linarith
        have hinv : (Real.log n)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        constructor
        · exact mul_nonneg (inv_nonneg.2 hpos.le) (vonMangoldtAP_nonneg M b n)
        · exact mul_le_mul hinv (vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n) (by norm_num)
  have hsum : ∑ n ∈ Icc 0 ⌊X⌋₊, (if ¬ n.Prime then Λ n else 0) = Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.2 ⟨by omega, hn.2⟩
    · intro n hn hn'
      have : n = 0 := by
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc] at hn'
        omega
      subst this
      simp
  have hpt := Chebyshev.psi_sub_theta_le hX
  rw [hpi, abs_sub_comm, ← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg fun n _ => (hterm n).1)]
  calc _ ≤ ∑ n ∈ Icc 0 ⌊X⌋₊, 2 * (if ¬ n.Prime then Λ n else 0) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = 2 * (Chebyshev.psi X - Chebyshev.theta X) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
