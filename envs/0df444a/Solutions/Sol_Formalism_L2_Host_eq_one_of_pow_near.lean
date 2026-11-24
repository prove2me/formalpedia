-- Prove2me | solution 1 for Formalism.L2.Host.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:34.353025+00:00
-- url     : https://prove2.me/submissions/a1d63964-e336-4085-baec-2586bf280dfa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
namespace Formalism.L2.Host
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hre : ∀ n : ℕ, 1 / 2 < (z ^ n).re := fun n => by
    have h1 := h n
    have h2 : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  have hsum_re : (N : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range N, z ^ i).re := by
    rw [Complex.re_sum]
    have h4 : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ ∑ i ∈ Finset.range N, (z ^ i).re :=
      Finset.sum_le_sum fun i _ => (hre i).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    exact h4
  have hsum_norm : ‖∑ i ∈ Finset.range N, z ^ i‖ < 1 / 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz, norm_div]
    exact div_lt_div_of_pos_right (h N) hpos
  have h5 := (hsum_re.trans (Complex.re_le_norm _)).trans_lt hsum_norm
  have h6 : (1 : ℝ) / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) * (1 / 2) := by ring
  rw [h6] at h5
  have h7 : (1 / ‖z - 1‖) * (1 / 2) < (N : ℝ) * (1 / 2) := by linarith
  linarith
end Formalism.L2.Host
