-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.newton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:08.642803+00:00
-- url     : https://prove2.me/submissions/7d6bb737-fe03-4782-8c8b-c0d7f4b40d2f

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_norm_intCast_le_one__7a067930451d
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_sum_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution {D : ℕ} {g : ℕ → ℚ_[p]} (hg : IVP p D g) :
    ∃ c : ℕ → ℤ_[p], ∀ m, g m = ∑ k ∈ range (D + 1), (c k : ℚ_[p]) * ((m.choose k : ℕ) : ℚ_[p]) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  set d : ℕ → ℚ_[p] := fun k => (fwdDiff 1)^[k] g 0 with hd
  have hd_sum : ∀ k, d k = ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ (k - i) * k.choose i) • g i := by
    intro k
    simp only [hd, fwdDiff_iter_eq_sum_shift, zero_add, smul_eq_mul, mul_one]
  have hd_norm : ∀ k, ‖d k‖ ≤ 1 := by
    intro k
    rw [hd_sum]
    apply norm_sum_le_one
    intro i _
    rw [zsmul_eq_mul, norm_mul]
    exact mul_le_one₀ (by exact_mod_cast norm_intCast_le_one' _) (norm_nonneg _) (hn i)
  have hd_zero : ∀ k, D < k → d k = 0 := by
    intro k hk
    have h0 : (fwdDiff (1 : ℚ_[p]))^[k] P.eval 0 = 0 := by
      rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]; rfl
    rw [fwdDiff_iter_eq_sum_shift] at h0
    rw [hd_sum, ← h0]
    apply sum_congr rfl
    intro i _
    rw [hPg]; simp
  refine ⟨fun k => ⟨d k, hd_norm k⟩, fun m => ?_⟩
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) g m 0
  simp only [zero_add, smul_eq_mul, mul_one] at hN
  rw [hN]
  change ∑ k ∈ range (m + 1), m.choose k • d k = ∑ k ∈ range (D + 1), (d k : ℚ_[p]) * ((m.choose k : ℕ) : ℚ_[p])
  have e1 : ∑ k ∈ range (m + 1), m.choose k • d k =
      ∑ k ∈ range (m + 1 + (D + 1)), m.choose k • d k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e2 : ∑ k ∈ range (D + 1), d k * ((m.choose k : ℕ) : ℚ_[p]) =
      ∑ k ∈ range (m + 1 + (D + 1)), d k * ((m.choose k : ℕ) : ℚ_[p]) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [hd_zero k (by omega)]; simp
  rw [e1, e2]
  apply sum_congr rfl
  intro k _
  rw [nsmul_eq_mul]; ring
end IVP
end Formalism.GM.gammaIntegralityLemmas
