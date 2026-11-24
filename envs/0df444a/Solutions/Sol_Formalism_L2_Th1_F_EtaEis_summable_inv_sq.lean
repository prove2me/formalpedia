-- Prove2me | solution 1 for Formalism.L2.Th1.F.EtaEis.summable_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:05.24438+00:00
-- url     : https://prove2.me/submissions/76a1b5a8-cf0a-435d-b842-d3b56bdd83aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace Formalism.L2.Th1.F
namespace EtaEis
private theorem summable_inv_sq_nat_mul_add (c w : ℂ) (hw : w ≠ 0) :
    Summable fun N : ℕ => 1 / ((N : ℂ) * w + c) ^ 2 := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ‖c‖ / ‖w‖)
  have hg : Summable fun N : ℕ => 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2) := by
    have h0 : Summable fun N : ℕ => 1 / (N : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact ((summable_nat_add_iff K).mpr h0).mul_left _
  refine (summable_nat_add_iff K).mp
    (Summable.of_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)))
  show ‖1 / (((N + K : ℕ) : ℂ) * w + c) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2)
  have hMK : K ≤ N + K := Nat.le_add_left K N
  generalize N + K = M at hMK ⊢
  have h1 : 2 * ‖c‖ / ‖w‖ < (M : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hMK)
  have h2 : 2 * ‖c‖ < (M : ℝ) * ‖w‖ := by
    exact (div_lt_iff₀ hw').mp h1
  have e : ‖(M : ℂ) * w‖ = (M : ℝ) * ‖w‖ := by
    simp
  have h4 : ‖(M : ℂ) * w‖ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := by
    calc ‖(M : ℂ) * w‖ = ‖((M : ℂ) * w + c) - c‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := norm_sub_le _ _
  rw [e] at h4
  have h3 : (M : ℝ) * ‖w‖ / 2 ≤ ‖(M : ℂ) * w + c‖ := by linarith [norm_nonneg c]
  have h5 : 0 < (M : ℝ) * ‖w‖ / 2 := by linarith [norm_nonneg c]
  have h6 : ((M : ℝ) * ‖w‖ / 2) ^ 2 ≤ ‖(M : ℂ) * w + c‖ ^ 2 := by
    rw [sq, sq]; exact mul_le_mul h3 h3 h5.le (norm_nonneg _)
  rw [norm_div, norm_one, norm_pow]
  calc 1 / ‖(M : ℂ) * w + c‖ ^ 2 ≤ 1 / ((M : ℝ) * ‖w‖ / 2) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos h5 2) h6
    _ = 4 / ‖w‖ ^ 2 * (1 / (M : ℝ) ^ 2) := by ring
end EtaEis
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EtaEis
namespace Formalism.L2.Th1.F.EtaEis
theorem _root_.solution (u v : ℂ) (hu : u ≠ 0) (n : ℤ) :
    Summable fun m : ℤ => 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hp : Summable fun N : ℕ => 1 / (((N : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) u hu).congr (fun N => ?_)
    simp only [Int.cast_natCast]
  have hm : Summable fun N : ℕ => 1 / (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr (fun N => ?_)
    rw [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg]
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨hp, hm⟩
end Formalism.L2.Th1.F.EtaEis
