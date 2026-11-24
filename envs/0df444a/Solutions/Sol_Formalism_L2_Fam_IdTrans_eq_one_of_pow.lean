-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:17.039571+00:00
-- url     : https://prove2.me/submissions/b28dfac7-b022-4714-9b26-3513376ca4f7

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
import Theorems.Thm_Formalism_L2_Fam_IdTrans_re_gt_half
import Theorems.Thm_Formalism_L2_Fam_IdTrans_one_sub_re_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution {a : ℂ} (h : ∀ n : ℤ, ‖a ^ n - 1‖ < 1) (ha : a ≠ 0) : a = 1 := by
  have hb : ∀ n : ℤ, ‖a‖ ^ n < 2 := fun n => by
    have h2 := h n
    rw [← norm_zpow]
    calc ‖a ^ n‖ = ‖(a ^ n - 1) + 1‖ := by ring_nf
      _ ≤ ‖a ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 2 := by rw [norm_one]; linarith
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h1 : ‖a‖ = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgt' : 1 < ‖a‖⁻¹ := (one_lt_inv₀ hpos).2 hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hgt'
      have h2 := hb (-(n : ℤ))
      rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
      linarith
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hgt
      have h2 := hb n
      rw [zpow_natCast] at h2
      linarith
  have hre : ∀ n : ℕ, 1 / 2 < (a ^ (2 ^ n)).re := fun n => by
    have hn := h ((2 ^ n : ℕ) : ℤ)
    rw [zpow_natCast] at hn
    exact re_gt_half (by rw [norm_pow, h1, one_pow]) hn
  have hd : ∀ n : ℕ, 3 ^ n * (1 - a.re) ≤ 1 - (a ^ (2 ^ n)).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hnorm : ‖a ^ (2 ^ n)‖ = 1 := by rw [norm_pow, h1, one_pow]
      have e : a ^ (2 ^ (n + 1)) = (a ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, one_sub_re_sq hnorm, pow_succ]
      have h3 := hre n
      have h4 : 0 ≤ 1 - (a ^ (2 ^ n)).re := by
        have h5 := Complex.re_le_norm (a ^ (2 ^ n))
        rw [hnorm] at h5
        linarith
      have h6 : 3 * (1 - (a ^ (2 ^ n)).re) ≤ 2 * (1 - (a ^ (2 ^ n)).re) * (1 + (a ^ (2 ^ n)).re) := by nlinarith
      nlinarith
  have hd0 : 1 - a.re ≤ 0 := by
    by_contra hpos0
    push_neg at hpos0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - a.re)) (by norm_num : (1 : ℝ) < 3)
    have h2 := hd n
    have h5 := hre n
    rw [div_lt_iff₀ hpos0] at hn
    linarith
  have hre1 : a.re = 1 := by
    have h5 := Complex.re_le_norm a
    rw [h1] at h5
    linarith
  have him : a.im = 0 := by
    have h0 := Complex.sq_norm a
    rw [h1, Complex.normSq_apply, hre1] at h0
    have h7 : a.im * a.im = 0 := by nlinarith
    exact mul_self_eq_zero.1 h7
  exact Complex.ext (by simp [hre1]) (by simp [him])
end Formalism.L2.Fam.IdTrans
