-- Prove2me | solution 1 for Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8f844b1c-331a-5d50-9300-37cbc52943e0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto

set_option autoImplicit false

namespace P2mLogBranch

open Filter Topology Complex

theorem main {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by

  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ s : ℝ, a < s → s < a + δ → ‖ℓ s - c‖ < ‖c‖ / 2 := by
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨δ, hδ, h⟩ := hlim (‖c‖ / 2) (half_pos hcpos)
    refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
    have h' := h (Set.mem_Ioi.mpr hs) (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith)
    rwa [dist_eq_norm] at h'

  set w : ℝ → ℂ := fun s => ℓ s / c with hw
  set Λ' : ℝ → ℂ := fun s => Complex.log (w s) + Complex.log c with hΛ'
  have hwball : ∀ s : ℝ, a < s → s < a + δ → ‖w s - 1‖ < 1 / 2 := by
    intro s hs hsδ
    have h1 : w s - 1 = (ℓ s - c) / c := by
      rw [hw]
      field_simp
    rw [h1, norm_div, div_lt_iff₀ hcpos]
    have := hδball s hs hsδ
    linarith
  have hw0 : ∀ s : ℝ, a < s → s < a + δ → w s ≠ 0 := by
    intro s hs hsδ h0
    have := hwball s hs hsδ
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith
  have hexp' : ∀ s : ℝ, a < s → s < a + δ → Complex.exp (Λ' s) = ℓ s := by
    intro s hs hsδ
    rw [hΛ', Complex.exp_add, Complex.exp_log (hw0 s hs hsδ), Complex.exp_log hc, hw]
    field_simp
  have hbound' : ∀ s : ℝ, a < s → s < a + δ → ‖Λ' s‖ ≤ 3 / 4 + ‖Complex.log c‖ := by
    intro s hs hsδ
    have h1 : ‖Complex.log (w s)‖ ≤ 3 / 4 := by
      have h2 := Complex.norm_log_one_add_half_le_self (z := w s - 1) (hwball s hs hsδ).le
      rw [add_sub_cancel] at h2
      have := hwball s hs hsδ
      linarith
    calc ‖Λ' s‖ ≤ ‖Complex.log (w s)‖ + ‖Complex.log c‖ := norm_add_le _ _
      _ ≤ 3 / 4 + ‖Complex.log c‖ := by linarith

  have hℓcont : ContinuousOn ℓ (Set.Ioi a) := by
    have : ContinuousOn (fun s => Complex.exp (Λ s)) (Set.Ioi a) := hΛ.cexp
    exact this.congr fun s hs => (hexp s hs).symm
  have hΛ'cont : ContinuousOn Λ' (Set.Ioo a (a + δ)) := by
    apply ContinuousOn.add _ continuousOn_const
    have hwcont : ContinuousOn w (Set.Ioo a (a + δ)) :=
      (hℓcont.mono Set.Ioo_subset_Ioi_self).div_const c
    refine ContinuousOn.comp (s := Set.Ioo a (a + δ)) (t := slitPlane) (g := Complex.log) ?_ hwcont ?_
    · intro z hz
      exact (continuousAt_clog hz).continuousWithinAt
    · intro s hs
      have h := Complex.mem_slitPlane_of_norm_lt_one (z := w s - 1)
        (by linarith [hwball s hs.1 hs.2])
      rwa [add_sub_cancel] at h

  set d : ℝ → ℂ := fun s => Λ s - Λ' s with hd
  have hdint : ∀ s : ℝ, a < s → s < a + δ → ∃ n : ℤ, d s = n * (2 * Real.pi * Complex.I) := by
    intro s hs hsδ
    have h1 : Complex.exp (d s) = 1 := by
      rw [hd]
      simp only
      rw [Complex.exp_sub, hexp s hs, hexp' s hs hsδ, div_self]
      rw [← hexp s hs]
      exact Complex.exp_ne_zero _
    exact Complex.exp_eq_one_iff.mp h1
  have hdcont : ContinuousOn d (Set.Ioo a (a + δ)) := (hΛ.mono Set.Ioo_subset_Ioi_self).sub hΛ'cont

  set f : ℝ → ℝ := fun s => (d s).im / (2 * Real.pi) with hf
  have hfcont : ContinuousOn f (Set.Ioo a (a + δ)) := by
    refine ContinuousOn.div_const ?_ _
    exact Complex.continuous_im.comp_continuousOn hdcont
  have hfint : ∀ s : ℝ, a < s → s < a + δ → ∃ n : ℤ, f s = n ∧ d s = n * (2 * Real.pi * Complex.I) := by
    intro s hs hsδ
    obtain ⟨n, hn⟩ := hdint s hs hsδ
    refine ⟨n, ?_, hn⟩
    rw [hf]
    simp only
    rw [hn]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
    field_simp
  have hfconst : ∀ s₁ s₂ : ℝ, a < s₁ → s₁ < a + δ → a < s₂ → s₂ < a + δ → f s₁ = f s₂ := by
    intro s₁ s₂ h1 h1' h2 h2'
    obtain ⟨n₁, hn₁, -⟩ := hfint s₁ h1 h1'
    obtain ⟨n₂, hn₂, -⟩ := hfint s₂ h2 h2'
    by_contra hne
    rw [hn₁, hn₂] at hne
    have hne' : n₁ ≠ n₂ := fun h => hne (by rw [h])

    set y : ℝ := (min n₁ n₂ : ℤ) + 1 / 2 with hy
    have hymem : y ∈ Set.uIcc (f s₁) (f s₂) := by
      rw [hn₁, hn₂, Set.mem_uIcc]
      rcases lt_or_gt_of_ne hne' with h | h
      · left
        have : min n₁ n₂ = n₁ := min_eq_left h.le
        rw [hy, this]
        constructor
        · linarith
        · have : (n₁ : ℝ) + 1 ≤ n₂ := by exact_mod_cast h
          linarith
      · right
        have : min n₁ n₂ = n₂ := min_eq_right h.le
        rw [hy, this]
        constructor
        · linarith
        · have : (n₂ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h
          linarith
    have hsub : Set.uIcc s₁ s₂ ⊆ Set.Ioo a (a + δ) := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      constructor
      · rcases ht with h | h <;> linarith [h.1]
      · rcases ht with h | h <;> linarith [h.2]
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc (hfcont.mono hsub) hymem
    obtain ⟨n, hn, -⟩ := hfint t (hsub ht).1 (hsub ht).2
    rw [hn, hy] at hft

    have h2 : (2 * n : ℤ) = 2 * min n₁ n₂ + 1 := by
      have : (2 : ℝ) * n = 2 * (min n₁ n₂ : ℤ) + 1 := by rw [hft]; ring
      exact_mod_cast this
    omega

  set s₀ : ℝ := a + δ / 2 with hs₀
  have hs₀a : a < s₀ := by rw [hs₀]; linarith
  have hs₀δ : s₀ < a + δ := by rw [hs₀]; linarith
  refine ⟨3 / 4 + ‖Complex.log c‖ + ‖d s₀‖, δ, hδ, fun s hs hsδ => ?_⟩
  have hds : d s = d s₀ := by
    obtain ⟨n, hn, hdn⟩ := hfint s hs hsδ
    obtain ⟨n₀, hn₀, hdn₀⟩ := hfint s₀ hs₀a hs₀δ
    have := hfconst s s₀ hs hsδ hs₀a hs₀δ
    rw [hn, hn₀] at this
    have hnn : n = n₀ := by exact_mod_cast this
    rw [hdn, hdn₀, hnn]
  have hΛeq : Λ s = Λ' s + d s := by rw [hd]; simp
  rw [hΛeq, hds]
  calc ‖Λ' s + d s₀‖ ≤ ‖Λ' s‖ + ‖d s₀‖ := norm_add_le _ _
    _ ≤ 3 / 4 + ‖Complex.log c‖ + ‖d s₀‖ := by linarith [hbound' s hs hsδ]

end P2mLogBranch

theorem solution
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C :=
  P2mLogBranch.main hΛ hexp hlim hc

end S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
end P2MW
export P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto (solution)
