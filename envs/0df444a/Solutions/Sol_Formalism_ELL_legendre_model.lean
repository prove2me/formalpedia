-- Prove2me | solution 1 for Formalism.ELL.legendre_model
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:09.18779+00:00
-- url     : https://prove2.me/submissions/347e2690-5965-4f3c-adaa-f56064939a2e

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Legendre
import Theorems.Thm_Formalism_ELL_LegendreModelEllipticTorsion_legPoly_natDegree
import Theorems.Thm_Formalism_ELL_LegendreModelEllipticTorsion_norm_one_add
import Theorems.Thm_Formalism_ELL_legendre_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open LegendreModelEllipticTorsion Polynomial
namespace Formalism.ELL
theorem _root_.solution : ModelLegendre := by
  intro K _ _ _ h2 j hj
  have h16 : ‖(16 : K)‖ = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256 : ‖(256 : K)‖ = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256ne : (256 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h256; exact zero_ne_one h256
  have hdeg : (legPoly j).degree ≠ 0 := by
    rw [degree_eq_natDegree, legPoly_natDegree h256ne]
    · decide
    · intro h0
      have := legPoly_natDegree h256ne j
      rw [h0, natDegree_zero] at this
      exact absurd this (by decide)
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : (256 : K) * (l ^ 2 - l + 1) ^ 3 = j * (l * (l - 1)) ^ 2 := by
    have := hl.eq_zero
    simp only [legPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  set t := l * (l - 1) with ht
  have hu : l ^ 2 - l + 1 = 1 + t := by rw [ht]; ring
  rw [hu] at hroot
  have hnorm := congrArg norm hroot
  simp only [norm_mul, norm_pow, h256, one_mul] at hnorm

  have htn : ‖t‖ = 1 := by
    by_contra hne
    have e := norm_one_add hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [e, max_eq_left hlt.le, one_pow] at hnorm
      have : ‖j‖ * ‖t‖ ^ 2 < 1 := by
        calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
      linarith
    · rw [e, max_eq_right hgt.le] at hnorm
      have hpos : 0 < ‖t‖ ^ 2 := by positivity
      have : ‖t‖ ^ 3 ≤ ‖t‖ ^ 2 := by
        rw [hnorm]; calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ = ‖t‖ ^ 2 := one_mul _
      have : ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1 := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      linarith
  have hprod : ‖l‖ * ‖l - 1‖ = 1 := by rw [← norm_mul, ← ht, htn]
  have hle1 : ‖l - 1‖ ≤ max ‖l‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max l (-1 : K)
    simpa [← sub_eq_add_neg] using this
  have hle2 : ‖l‖ ≤ max ‖l - 1‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max (l - 1) (1 : K)
    simpa using this
  have hl1 : ‖l‖ = 1 := by
    rcases lt_trichotomy ‖l‖ 1 with h | h | h
    · exfalso
      rw [max_eq_right h.le] at hle1
      have : ‖l‖ * ‖l - 1‖ < 1 := by
        calc ‖l‖ * ‖l - 1‖ ≤ ‖l‖ * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact h
      linarith
    · exact h
    · exfalso
      have hpos : 0 < ‖l‖ := by linarith
      have hlt : ‖l - 1‖ < 1 := by
        by_contra hc
        rw [not_lt] at hc
        nlinarith
      rw [max_eq_right hlt.le] at hle2
      linarith
  have hl2 : ‖l - 1‖ = 1 := by rw [hl1, one_mul] at hprod; exact hprod
  obtain ⟨hΔ, hc4⟩ := legendre_invariant K l
  refine ⟨l, hl1, hl2, ?_, ?_⟩
  · rw [hΔ, hc4]
    have : (l ^ 2 - l + 1) = 1 + t := hu
    rw [this]
    have e2 : (16 : K) * l ^ 2 * (l - 1) ^ 2 = 16 * t ^ 2 := by rw [ht]; ring
    rw [e2]
    linear_combination 16 * hroot
  · rw [hΔ, norm_mul, norm_mul, h16, norm_pow, norm_pow, hl1, hl2]
    norm_num
end Formalism.ELL
