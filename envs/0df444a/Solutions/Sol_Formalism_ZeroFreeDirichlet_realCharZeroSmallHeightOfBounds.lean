-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.realCharZeroSmallHeightOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:30.017088+00:00
-- url     : https://prove2.me/submissions/7971ee11-279f-4792-83aa-de2fbc35f5c5

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealSmallTOf
import Theorems.Thm_P2M_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos__2a434b05b21b
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_ofReal_sub
import Theorems.Thm_Formalism_ZeroFreeDirichlet_mul_le_div_sq_add_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : RealSmallTOf := by
  intro hLZ hLD hPos hConj
  obtain ⟨C, hC⟩ := hLZ
  obtain ⟨C₀, hC₀, hLD⟩ := hLD
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set K : ℝ := 2 * C₀ + Cp with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set W : ℝ := 10 * (K + 1) with hW
  have hW10 : 10 ≤ W := by rw [hW]; linarith
  have hWpos : 0 < W := by linarith
  refine ⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩
  intro q _ χ hχ2 hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

  obtain ⟨Z, m, hZ, hm1, hm2, hb⟩ := hC q χ hχ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb
  set L₀ := Real.log ((q : ℝ) * 2) with hL₀
  have hlog2 := Real.log_two_gt_d9
  have hL₀2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
  have hL₀h : 1 / 2 < L₀ := by norm_num at hlog2; linarith
  have hL₀pos : 0 < L₀ := by linarith
  set T : ℝ := W * L₀ with hT
  have hTpos : 0 < T := mul_pos hWpos hL₀pos
  have hT5 : 5 ≤ T := by rw [hT]; nlinarith
  have hTe : T = 10 * (K * L₀) + 10 * L₀ := by rw [hT, hW]; ring
  have hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀ := by rw [hK]; ring
  set σ : ℝ := 1 + 1 / T with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / T := by positivity
    linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : 1 / T ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hT5
    linarith

  have hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀ := by
    have hP := (hPos q σ hσ1).2.1 χ hχ2
    have h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀ := by
      have h := hLD q 1 (σ : ℂ) (by simpa using hσ1)
      have e : 1 / ((σ : ℂ).re - 1) = T := by
        rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]
      rw [e] at h
      exact (Complex.re_le_norm _).trans h
    have h1 := hb σ hσ1 hσ2
    have h2 : C * L₀ ≤ Cp * L₀ := mul_le_mul_of_nonneg_right hCCp hL₀pos.le
    have h3 : C₀ ≤ 2 * (C₀ * L₀) := by nlinarith
    have h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀ := by ring
    rw [h4]
    linarith

  have hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le

  have hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re := by
    intro ρ hi hr hz
    unfold InRegion at hr
    obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hLρdef] at hi hr
    have hLρ : L₀ ≤ Lρ := by
      rw [hLρdef, hL₀]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T) := by
      have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ
      have e : 1 / (10 * W) / L₀ = 1 / (10 * T) := by rw [hT, div_div, mul_assoc]
      linarith
    have hβ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz
    have hβ : 1 - 1 / (10 * T) ≤ ρ.re := by linarith
    have hγ : |ρ.im| ≤ 1 / (10 * T) := by linarith
    have hsmall : 1 / (10 * T) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hTT : T * (1 / (10 * T)) = 1 / 10 := by field_simp
    refine ⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by push_cast; rfl
      rw [e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      have : |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · rw [re_one_div_ofReal_sub]
      have hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1 := by
        rw [hσ]; field_simp; ring
      have hA : 0 < T * (1 - ρ.re) := mul_pos hTpos (by linarith)
      have hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T)) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      apply mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos
      · rw [hTσ]; linarith
      · rw [hTσ]; linarith
      · rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hγ hTpos.le
        linarith
  have hbig : (11 * K + 10) * L₀ < 8 / 5 * T := by
    have : 0 ≤ K * L₀ := mul_nonneg hK0 hL₀pos.le
    nlinarith

  have htwo : ∀ ρ₁ ρ₂ : ℂ,
      (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) →
      (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ ρ₂ = 0) →
      ρ₁ ≠ ρ₂ → False := by
    rintro ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne
    obtain ⟨h1Z, h1r⟩ := hcons ρ₁ a1 b1 c1
    obtain ⟨h2Z, h2r⟩ := hcons ρ₂ a2 b2 c2
    have hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1Z
      · exact h2Z
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)
    rw [Finset.sum_pair hne] at hs
    have hm1' : (1 : ℝ) ≤ m ρ₁ := by exact_mod_cast hm1 ρ₁ h1Z
    have hm2' : (1 : ℝ) ≤ m ρ₂ := by exact_mod_cast hm1 ρ₂ h2Z
    have hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re := by linarith
    have hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]

  have hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      deriv (DirichletCharacter.LFunction χ) ρ = 0 → False := by
    intro ρ a b c hd
    obtain ⟨hρZ, hρr⟩ := hcons ρ a b c
    have hs := Finset.single_le_sum hnn hρZ
    have hm : (2 : ℝ) ≤ m ρ := by exact_mod_cast hm2 ρ hρZ hd
    have hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hr]
  intro s s' hs hs' hrs hrs' hz hz'
  have hsim : s.im = 0 := by
    by_contra hne
    refine htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_
    · simpa [Complex.conj_im, abs_neg] using hs
    · unfold InRegion at hrs ⊢
      simpa [Complex.conj_re, Complex.conj_im, abs_neg] using hrs
    · rw [hConj q χ hχ2 hχ s, hz, map_zero]
    · intro h
      apply hne
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  refine ⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩
  by_contra hne
  exact htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne
end Formalism.ZeroFreeDirichlet
