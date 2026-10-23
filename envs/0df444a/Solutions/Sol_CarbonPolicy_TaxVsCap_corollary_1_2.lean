-- Prove2me | solution 2 for CarbonPolicy.TaxVsCap.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T21:36:22.327498+00:00
-- url     : https://prove2.me/submissions/f96fc53d-f77f-4daf-9ba6-2dc827c7ab7d

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
import Theorems.Thm_CarbonPolicy_TaxVsCap_moment_tax
import Theorems.Thm_CarbonPolicy_TaxVsCap_moment_cap
import Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_1
import Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_2
import Theorems.Thm_CarbonPolicy_TaxVsCap_emission_difference

open ProbabilityTheory MeasureTheory

namespace CarbonCor1Aux
open CarbonPolicy.TaxVsCap

/-- 8b times the consumer-surplus difference `CS_T - CS_C`, as a function of `ρ`. -/
noncomputable def dCS (b β γp A K D S ρ : ℝ) : ℝ :=
  (A - gammaT0 b β γp A K * K) ^ 2 - (A - gammaC0 b β γp A K D S ρ * K) ^ 2
    - (gammaC0 b β γp A K D S ρ) ^ 2 * S ^ 2
    + 2 * gammaC0 b β γp A K D S ρ * (ρ * D * S)

lemma quad (a b c x0 : ℝ) (ha : a < 0) (h0 : 0 < a * x0 ^ 2 + b * x0 + c) :
    ∃ r1 r2 : ℝ, ∀ x : ℝ, 0 < a * x ^ 2 + b * x + c ↔ r1 < x ∧ x < r2 := by
  have hd : 0 < b ^ 2 - 4 * a * c := by
    nlinarith [sq_nonneg (2 * a * x0 + b), mul_neg_of_neg_of_pos ha h0]
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = b ^ 2 - 4 * a * c :=
    ⟨Real.sqrt (b ^ 2 - 4 * a * c), Real.sqrt_pos.mpr hd, Real.sq_sqrt hd.le⟩
  refine ⟨(s - b) / (2 * a), (-s - b) / (2 * a), fun x => ?_⟩
  have h2a : 2 * a < 0 := by linarith
  rw [div_lt_iff_of_neg h2a, lt_div_iff_of_neg h2a]
  constructor
  · intro h
    have h1 : (2 * a * x + b) ^ 2 < s ^ 2 := by nlinarith [mul_neg_of_neg_of_pos ha h]
    have h2 := abs_lt.mp (abs_lt_of_sq_lt_sq h1 hs0.le)
    constructor <;> nlinarith [h2.1, h2.2]
  · rintro ⟨h1, h2⟩
    have h3 : (2 * a * x + b) ^ 2 < s ^ 2 := by
      nlinarith [mul_pos (show 0 < s - (2 * a * x + b) by linarith)
        (show 0 < s + (2 * a * x + b) by linarith)]
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le hneg]

lemma gC_int {b β γp A K D S ρ : ℝ} (h : A * K + ρ * D * S > (K ^ 2 + S ^ 2) * γp) :
    gammaC0 b β γp A K D S ρ =
      (4 * b * β * γp - A * K - ρ * D * S) / (4 * b * β - K ^ 2 - S ^ 2) := by
  unfold gammaC0; rw [if_pos h]

lemma gC_cor {b β γp A K D S ρ : ℝ} (h : ¬ (A * K + ρ * D * S > (K ^ 2 + S ^ 2) * γp)) :
    gammaC0 b β γp A K D S ρ = γp := by
  unfold gammaC0; rw [if_neg h]

/-- Generic identity: `8b(CS_T-CS_C) - 4bβ(...) = 4b(Π_T - Π_C)` in moment form. -/
lemma key_id (b β γp A K S gT g c : ℝ)
    (hgT : gT * (4 * b * β - K ^ 2) = 4 * b * β * γp - A * K) :
    (A - gT * K) ^ 2 - (A - g * K) ^ 2 - g ^ 2 * S ^ 2 + 2 * g * c
      = gT ^ 2 * (4 * b * β - K ^ 2)
        - (2 * (4 * b * β * γp - A * K - c) * g - (4 * b * β - K ^ 2 - S ^ 2) * g ^ 2)
        + 4 * b * β * ((γp - gT) ^ 2 - (γp - g) ^ 2) := by
  linear_combination (-2 * gT) * hgT

set_option maxHeartbeats 4000000 in
theorem pure_main (b β γp A K D S : ℝ)
    (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K)
    (hD : 0 < D) (hS : 0 < S)
    (hcurvature : K ^ 2 + S ^ 2 < 4 * b * β)
    (hinvestment : A * K < 4 * b * β * γp)
    (hdemand : γp * K < A) :
    R b β γp A K D S < R0 b β γp A K D S ∧
    0 < dCS b β γp A K D S (R b β γp A K D S) ∧
    0 < dCS b β γp A K D S (R0 b β γp A K D S) ∧
    (∀ ρ : ℝ, (ρ < R0 b β γp A K D S → gammaT0 b β γp A K < gammaC0 b β γp A K D S ρ) ∧
      (R0 b β γp A K D S < ρ → gammaC0 b β γp A K D S ρ < gammaT0 b β γp A K)) ∧
    ∃ R1 R2 : ℝ, ∀ ρ : ℝ, 0 < dCS b β γp A K D S ρ ↔ R1 < ρ ∧ ρ < R2 := by
  have hE : 0 < 4 * b * β - K ^ 2 := by linarith [sq_nonneg S]
  have hDp : 0 < 4 * b * β - K ^ 2 - S ^ 2 := by linarith
  have hN : 0 < 4 * b * β * γp - A * K := by linarith
  have hP : 0 < D * S := mul_pos hD hS
  have hbβ : 0 < 4 * b * β := by linarith [sq_nonneg K]
  set E := 4 * b * β - K ^ 2 with hEdef
  set Dp := 4 * b * β - K ^ 2 - S ^ 2 with hDpdef
  set N := 4 * b * β * γp - A * K with hNdef
  set P := D * S with hPdef
  set gT := gammaT0 b β γp A K with hgTdef
  have hgT : gT * E = N := by
    rw [hgTdef]; unfold gammaT0
    exact div_mul_cancel₀ _ hE.ne'
  have hgTpos : 0 < gT := by
    by_contra h; push_neg at h; linarith [mul_nonpos_of_nonpos_of_nonneg h hE.le]
  have hgTlt : gT < γp := by
    by_contra h; push_neg at h
    have : γp * E ≤ gT * E := mul_le_mul_of_nonneg_right h hE.le
    have e : γp * E = 4 * b * β * γp - γp * K ^ 2 := by rw [hEdef]; ring
    linarith [mul_lt_mul_of_pos_right hdemand hK]
  have hDpE : Dp = E - S ^ 2 := by rw [hDpdef, hEdef]
  -- R0 in c-units
  have hR0 : R0 b β γp A K D S * P = S ^ 2 * gT := by
    unfold R0; rw [← hgTdef, hPdef]; field_simp
  -- general facts on gammaC0
  have hint : ∀ ρ : ℝ, (4 * b * β * γp - A * K) - Dp * γp < ρ * P →
      gammaC0 b β γp A K D S ρ * Dp = N - ρ * P := by
    intro ρ h
    have hc : A * K + ρ * D * S > (K ^ 2 + S ^ 2) * γp := by
      have : ρ * D * S = ρ * P := by rw [hPdef]; ring
      rw [this]; rw [hDpdef] at h; linarith
    rw [gC_int hc]
    have hDp' : (4 * b * β - K ^ 2 - S ^ 2) ≠ 0 := hDp.ne'
    rw [hPdef, hDpdef, hNdef]; field_simp
  have hcor : ∀ ρ : ℝ, ρ * P ≤ (4 * b * β * γp - A * K) - Dp * γp →
      gammaC0 b β γp A K D S ρ = γp := by
    intro ρ h
    apply gC_cor
    have : ρ * D * S = ρ * P := by rw [hPdef]; ring
    rw [this]; rw [hDpdef] at h; push_neg; linarith
  -- dCS via key identity
  have hdCS : ∀ ρ : ℝ, dCS b β γp A K D S ρ =
      gT ^ 2 * E - (2 * (N - ρ * P) * gammaC0 b β γp A K D S ρ
        - Dp * (gammaC0 b β γp A K D S ρ) ^ 2)
      + 4 * b * β * ((γp - gT) ^ 2 - (γp - gammaC0 b β γp A K D S ρ) ^ 2) := by
    intro ρ
    unfold dCS
    rw [← hgTdef]
    have := key_id b β γp A K S gT (gammaC0 b β γp A K D S ρ) (ρ * D * S) (by rw [hgT])
    rw [this, hEdef, hNdef, hDpdef, hPdef]; ring
  -- P3: value at R0
  have hR0int : (4 * b * β * γp - A * K) - Dp * γp < R0 b β γp A K D S * P := by
    have e : Dp * gT = gT * E - S ^ 2 * gT := by rw [hDpE]; ring
    rw [hR0]; linarith [mul_lt_mul_of_pos_left hgTlt hDp]
  have hgR0 : gammaC0 b β γp A K D S (R0 b β γp A K D S) = gT := by
    have h1 := hint _ hR0int
    rw [hR0] at h1
    have : gT * Dp = N - S ^ 2 * gT := by rw [hDpE]; linear_combination hgT
    exact mul_right_cancel₀ hDp.ne' (h1.trans this.symm)
  have P3 : 0 < dCS b β γp A K D S (R0 b β γp A K D S) := by
    rw [hdCS, hgR0, hR0]
    have : gT ^ 2 * E - (2 * (N - S ^ 2 * gT) * gT - Dp * gT ^ 2) = gT ^ 2 * S ^ 2 := by
      rw [hDpE]; linear_combination (2 * gT) * hgT
    rw [this]; simp; positivity
  -- rho0 existence and spec
  have hkey : ∀ r : ℝ, (N - r * P) ^ 2 * E - N ^ 2 * Dp =
      (N * P * E) * (R0 b β γp A K D S + D * S * r ^ 2 / (4 * b * β * γp - A * K) - 2 * r) := by
    intro r
    have h1 : R0 b β γp A K D S = S ^ 2 * gT / P := by
      rw [← hR0]; field_simp
    have e1 : N * P * E * (S ^ 2 * gT / P) = N * E * S ^ 2 * gT := by field_simp
    have e2 : N * P * E * (D * S * r ^ 2 / (4 * b * β * γp - A * K)) = P * E * P * r ^ 2 := by
      rw [← hNdef, hPdef]; field_simp
    have e3 : N * P * E * (S ^ 2 * gT / P + D * S * r ^ 2 / (4 * b * β * γp - A * K) - 2 * r)
        = N * E * S ^ 2 * gT + P * E * P * r ^ 2 - N * P * E * (2 * r) := by
      rw [mul_sub, mul_add, e1, e2]
    rw [h1, e3, hDpE]
    linear_combination (-(N * S ^ 2)) * hgT
  have hex : ∃ r : ℝ, r < (4 * b * β * γp - A * K) / (D * S) ∧
      R0 b β γp A K D S + D * S * r ^ 2 / (4 * b * β * γp - A * K) - 2 * r = 0 := by
    obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 * E = Dp := by
      refine ⟨Real.sqrt (Dp / E), Real.sqrt_pos.mpr (div_pos hDp hE), ?_⟩
      rw [Real.sq_sqrt (div_pos hDp hE).le]; field_simp
    refine ⟨N * (1 - t) / P, ?_, ?_⟩
    · show N * (1 - t) / P < N / P
      rw [div_lt_div_iff_of_pos_right hP]; linarith [mul_pos hN ht0]
    · have h := hkey (N * (1 - t) / P)
      have hz : (N - N * (1 - t) / P * P) ^ 2 * E - N ^ 2 * Dp = 0 := by
        rw [div_mul_cancel₀ _ hP.ne', ← ht]; ring
      rw [hz] at h
      have hNPE : N * P * E ≠ 0 := by positivity
      exact (mul_eq_zero.mp h.symm).resolve_left hNPE
  obtain ⟨hr0lt, hr0eq⟩ : rho0 b β γp A K D S < (4 * b * β * γp - A * K) / (D * S) ∧
      R0 b β γp A K D S + D * S * (rho0 b β γp A K D S) ^ 2 / (4 * b * β * γp - A * K)
        - 2 * rho0 b β γp A K D S = 0 := by
    unfold rho0
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  set r0 := rho0 b β γp A K D S with hr0def
  have hcN : r0 * P < N := (lt_div_iff₀ hP).mp hr0lt
  have hsq : (N - r0 * P) ^ 2 * E = N ^ 2 * Dp := by
    have hk := hkey r0
    rw [hr0eq, mul_zero] at hk; linarith
  have hD' : D ≠ 0 := hD.ne'
  have hS' : S ≠ 0 := hS.ne'
  have hrhoC : rhoC γp A K D S * P = (4 * b * β * γp - A * K) - Dp * γp := by
    unfold rhoC; rw [hDpdef, hPdef]; field_simp; ring
  have hgTDp : gT * Dp = N - S ^ 2 * gT := by rw [hDpE]; linear_combination hgT
  have P12 : R b β γp A K D S < R0 b β γp A K D S ∧ 0 < dCS b β γp A K D S (R b β γp A K D S) := by
    by_cases h0 : rho0 b β γp A K D S > rhoC γp A K D S
    · have hR : R b β γp A K D S = r0 := by unfold R; rw [if_pos h0]
      have hin : (4 * b * β * γp - A * K) - Dp * γp < r0 * P := by
        rw [← hrhoC]; exact (mul_lt_mul_iff_left₀ hP).mpr h0
      have hg := hint r0 hin
      have hlt : r0 * P < S ^ 2 * gT := by
        by_contra hc; push_neg at hc
        have hle : N - r0 * P ≤ gT * Dp := by rw [hgTDp]; linarith
        have h1 : (N - r0 * P) ^ 2 ≤ (gT * Dp) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hle 2
        have h2 := mul_le_mul_of_nonneg_right h1 hE.le
        have h3 : N ^ 2 * Dp = gT ^ 2 * E ^ 2 * Dp := by rw [← hgT]; ring
        have h4 : 0 < gT ^ 2 * E * Dp * S ^ 2 := by positivity
        have h5 : gT ^ 2 * E * Dp * (E - Dp) = gT ^ 2 * E * Dp * S ^ 2 := by rw [hDpE]; ring
        have h6 : gT ^ 2 * E ^ 2 * Dp ≤ gT ^ 2 * Dp ^ 2 * E := by
          have : (gT * Dp) ^ 2 * E = gT ^ 2 * Dp ^ 2 * E := by ring
          linarith
        have h7 : gT ^ 2 * E * Dp * (E - Dp) = gT ^ 2 * E ^ 2 * Dp - gT ^ 2 * Dp ^ 2 * E := by ring
        linarith
      refine ⟨?_, ?_⟩
      · rw [hR, ← mul_lt_mul_iff_left₀ hP, hR0]; exact hlt
      · rw [hR, hdCS]
        set g := gammaC0 b β γp A K D S r0 with hgdef
        have hgg : g ^ 2 * Dp = gT ^ 2 * E := by
          have h1 : (g * Dp) ^ 2 * E = (gT * E) ^ 2 * Dp := by rw [hg, hgT]; exact hsq
          have h2 : (g ^ 2 * Dp) * (Dp * E) = (gT ^ 2 * E) * (Dp * E) := by linear_combination h1
          exact mul_right_cancel₀ (by positivity) h2
        have hgl : g < γp := by
          by_contra hc; push_neg at hc
          have := mul_le_mul_of_nonneg_left hc hDp.le
          linarith
        have hgr : gT < g := by
          by_contra hc; push_neg at hc
          have := mul_le_mul_of_nonneg_left hc hDp.le
          linarith
        rw [← hg]
        have h3 : 0 < (γp - gT) ^ 2 - (γp - g) ^ 2 := by
          have := mul_pos (sub_pos.mpr hgr) (show 0 < 2 * γp - gT - g by linarith)
          linarith
        linarith [mul_pos hbβ h3]
    · have hR : R b β γp A K D S = rho1 b β γp A K D S := by unfold R; rw [if_neg h0]
      push_neg at h0
      have hle : r0 * P ≤ (4 * b * β * γp - A * K) - Dp * γp := by
        rw [← hrhoC]; exact mul_le_mul_of_nonneg_right h0 hP.le
      have hineq : Dp * γp ^ 2 ≤ gT ^ 2 * E := by
        have h1 : (Dp * γp) ^ 2 ≤ (N - r0 * P) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        have h2 := mul_le_mul_of_nonneg_right h1 hE.le
        have h3 : N ^ 2 * Dp = gT ^ 2 * E ^ 2 * Dp := by rw [← hgT]; ring
        have h4 : (Dp * γp ^ 2) * (Dp * E) ≤ (gT ^ 2 * E) * (Dp * E) := by linarith
        exact le_of_mul_le_mul_right h4 (by positivity)
      have hrho1 : rho1 b β γp A K D S * P * (2 * γp * E) =
          2 * N * γp * E - Dp * E * γp ^ 2 - N ^ 2 := by
        have hγp' : γp ≠ 0 := hγp.ne'
        have hE' : (4 * b * β - K ^ 2) ≠ 0 := hE.ne'
        unfold rho1; rw [hPdef, hEdef, hDpdef, hNdef]; field_simp; ring
      set c1 := rho1 b β γp A K D S * P with hc1def
      have hc1 : c1 ≤ (4 * b * β * γp - A * K) - Dp * γp := by
        have h1 : c1 * (2 * γp * E) ≤ ((4 * b * β * γp - A * K) - Dp * γp) * (2 * γp * E) := by
          rw [hrho1, ← hNdef]
          have h3 : N ^ 2 = gT ^ 2 * E ^ 2 := by rw [← hgT]; ring
          linarith [mul_le_mul_of_nonneg_right hineq hE.le]
        exact le_of_mul_le_mul_right h1 (by positivity)
      have hgc := hcor _ hc1
      refine ⟨?_, ?_⟩
      · rw [hR, ← mul_lt_mul_iff_left₀ hP, hR0]
        have := mul_lt_mul_of_pos_left hgTlt hDp
        linarith
      · rw [hR, hdCS, hgc]
        have hz : gT ^ 2 * E - (2 * (N - c1) * γp - Dp * γp ^ 2) = 0 := by
          have h1 : (gT ^ 2 * E - (2 * (N - c1) * γp - Dp * γp ^ 2)) * E = 0 := by
            have h3 : N ^ 2 = gT ^ 2 * E ^ 2 := by rw [← hgT]; ring
            linear_combination hrho1 - h3
          rcases mul_eq_zero.mp h1 with h | h
          · exact h
          · exact absurd h hE.ne'
        have h5 : 0 < (γp - gT) ^ 2 := by have := sub_pos.mpr hgTlt; positivity
        linarith [mul_pos hbβ h5]
  have hord : ∀ ρ : ℝ, (ρ < R0 b β γp A K D S → gT < gammaC0 b β γp A K D S ρ) ∧
      (R0 b β γp A K D S < ρ → gammaC0 b β γp A K D S ρ < gT) := by
    intro ρ
    constructor
    · intro h
      have hρ : ρ * P < S ^ 2 * gT := by rw [← hR0]; exact mul_lt_mul_of_pos_right h hP
      by_cases hin : (4 * b * β * γp - A * K) - Dp * γp < ρ * P
      · have hg := hint ρ hin
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hDp.le
        linarith
      · push_neg at hin
        rw [hcor ρ hin]; exact hgTlt
    · intro h
      have hρ : S ^ 2 * gT < ρ * P := by rw [← hR0]; exact mul_lt_mul_of_pos_right h hP
      have hin : (4 * b * β * γp - A * K) - Dp * γp < ρ * P := by
        rw [hR0] at hR0int; linarith
      have hg := hint ρ hin
      by_contra hc; push_neg at hc
      have := mul_le_mul_of_nonneg_left hc hDp.le
      linarith
  refine ⟨P12.1, P12.2, P3, hord, ?_⟩
  -- the quadratic G
  set W := 8 * b * β - K ^ 2 - S ^ 2 with hWdef
  have hW : 0 < W := by linarith
  set Gf : ℝ → ℝ := fun x => -W * x ^ 2 + 8 * b * β * γp * x + ((A - gT * K) ^ 2 - A ^ 2)
    with hGfdef
  have hGgT : Gf gT = gT ^ 2 * S ^ 2 := by
    simp only [hGfdef, hWdef]; linear_combination (-2 * gT) * hgT
  obtain ⟨g1, g2, hq⟩ := quad (-W) (8 * b * β * γp) ((A - gT * K) ^ 2 - A ^ 2) gT
    (by linarith) (by have := hGgT; simp only [hGfdef] at this; rw [this]; positivity)
  have hq' : ∀ x, 0 < Gf x ↔ g1 < x ∧ x < g2 := fun x => hq x
  have hg12 := (hq' gT).mp (by rw [hGgT]; positivity)
  -- interior and corner identities
  have hIntId : ∀ ρ : ℝ, gammaC0 b β γp A K D S ρ * Dp = N - ρ * P →
      dCS b β γp A K D S ρ = Gf (gammaC0 b β γp A K D S ρ) := by
    intro ρ hg
    rw [hdCS, ← hg]
    simp only [hGfdef, hWdef, hEdef, hDpdef]
    linear_combination (2 * gT) * hgT
  have hCorId : ∀ ρ : ℝ, gammaC0 b β γp A K D S ρ = γp →
      dCS b β γp A K D S ρ = Gf γp + 2 * γp * (ρ * P - ((4 * b * β * γp - A * K) - Dp * γp)) := by
    intro ρ hg
    rw [hdCS, hg]
    simp only [hGfdef, hWdef, hEdef, hDpdef, hNdef]
    linear_combination (2 * gT) * hgT
  by_cases hGp : 0 < Gf γp
  · have hgp := (hq' γp).mp hGp
    obtain ⟨q, hq2⟩ : ∃ q : ℝ, q * (2 * γp) = Gf γp := ⟨Gf γp / (2 * γp), by field_simp⟩
    have hqpos : 0 < q := by
      by_contra hc; push_neg at hc
      linarith [mul_nonpos_of_nonpos_of_nonneg hc (by linarith : (0:ℝ) ≤ 2 * γp)]
    refine ⟨((4 * b * β * γp - A * K) - Dp * γp - q) / P, (N - Dp * g1) / P, fun ρ => ?_⟩
    rw [div_lt_iff₀ hP, lt_div_iff₀ hP]
    by_cases hin : (4 * b * β * γp - A * K) - Dp * γp < ρ * P
    · have hg := hint ρ hin
      rw [hIntId ρ hg, hq']
      have hgl : gammaC0 b β γp A K D S ρ < γp := by
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hDp.le
        linarith
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by linarith, ?_⟩
        have := mul_lt_mul_of_pos_left h1 hDp
        linarith
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith⟩
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hDp.le
        linarith
    · push_neg at hin
      rw [hCorId ρ (hcor ρ hin), ← hq2]
      have := mul_lt_mul_of_pos_left hgp.1 hDp
      constructor
      · intro h
        refine ⟨?_, by linarith⟩
        by_contra hc; push_neg at hc
        linarith [mul_nonneg hγp.le (show 0 ≤ (4 * b * β * γp - A * K) - Dp * γp - q - ρ * P by linarith)]
      · rintro ⟨h1, h2⟩
        linarith [mul_pos hγp (show 0 < ρ * P - ((4 * b * β * γp - A * K) - Dp * γp - q) by linarith)]
  · push_neg at hGp
    have hg2 : g2 ≤ γp := by
      by_contra hc; push_neg at hc
      have := (hq' γp).mpr ⟨by linarith [hg12.1], hc⟩
      linarith
    refine ⟨(N - Dp * g2) / P, (N - Dp * g1) / P, fun ρ => ?_⟩
    rw [div_lt_iff₀ hP, lt_div_iff₀ hP]
    by_cases hin : (4 * b * β * γp - A * K) - Dp * γp < ρ * P
    · have hg := hint ρ hin
      rw [hIntId ρ hg, hq']
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · have := mul_lt_mul_of_pos_left h2 hDp
          linarith
        · have := mul_lt_mul_of_pos_left h1 hDp
          linarith
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra hc; push_neg at hc
          have := mul_le_mul_of_nonneg_left hc hDp.le
          linarith
        · by_contra hc; push_neg at hc
          have := mul_le_mul_of_nonneg_left hc hDp.le
          linarith
    · push_neg at hin
      rw [hCorId ρ (hcor ρ hin)]
      constructor
      · intro h
        exfalso
        linarith [mul_nonneg hγp.le (show 0 ≤ (4 * b * β * γp - A * K) - Dp * γp - ρ * P by linarith)]
      · rintro ⟨h1, h2⟩
        exfalso
        have := mul_le_mul_of_nonneg_left hg2 hDp.le
        linarith

lemma CST_eq {Ω : Type} [MeasurableSpace Ω] (M : Model Ω) (b β γp γ : ℝ) (hb : 0 < b) :
    CST M b γ = ((abar M.P M.a - γ * kbar M.P M.k) ^ 2 + (sigmaD M.P M.a) ^ 2) / (8 * b) := by
  have h1 : CST M b γ = (1 / 2) * (PiT M b β γp 0 γ + β * (γp - γ) ^ 2) := by
    unfold CST PiT
    rw [sub_add_cancel, ← integral_const_mul]
    congr 1; funext ω
    unfold profit qStar; field_simp; ring
  rw [h1, moment_tax M b β γp 0 hb γ]; field_simp; ring

lemma CSC_eq {Ω : Type} [MeasurableSpace Ω] (M : Model Ω) (b β γp γ : ℝ) (hb : 0 < b) :
    CSC M b γ = ((abar M.P M.a - γ * kbar M.P M.k) ^ 2 + (sigmaD M.P M.a) ^ 2
      + (γ ^ 2 * (sigma M.P M.k) ^ 2 - 2 * γ * (rho M.P M.a M.k) *
          (sigmaD M.P M.a) * (sigma M.P M.k))) / (8 * b) := by
  have h1 : CSC M b γ = (1 / 2) * (PiC M b β γp 0 γ + β * (γp - γ) ^ 2) := by
    unfold CSC PiC
    rw [sub_add_cancel, ← integral_const_mul]
    congr 1; funext ω
    unfold profit qStar; field_simp; ring
  rw [h1, moment_cap M b β γp 0 hb γ]; field_simp; ring

end CarbonCor1Aux

open CarbonPolicy.TaxVsCap in
theorem solution (b β γp w A K D S : ℝ)
    (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K)
    (hD : 0 < D) (hS : 0 < S)
    (hcurvature : K ^ 2 + S ^ 2 < 4 * b * β)
    (hinvestment : A * K < 4 * b * β * γp)
    (hdemand : γp * K < A) :
    (∃ R1 R2 : ℝ,
      R1 < R b β γp A K D S ∧ R b β γp A K D S < R0 b β γp A K D S ∧ R0 b β γp A K D S < R2 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (M : Model Ω)
        (hbarA : abar M.P M.a = A) (hbarK : kbar M.P M.k = K)
      (hsD : sigmaD M.P M.a = D) (hs : sigma M.P M.k = S)
      (hA : Assumption1 M b β γp) (γT γC : ℝ)
      (hT : OptimalTax M b β γp w γT)
      (hC : OptimalCap M b β γp w γC),
        (CSC M b γC < CST M b γT ↔
          R1 < rho M.P M.a M.k ∧ rho M.P M.a M.k < R2)) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (M : Model Ω)
      (hbarA : abar M.P M.a = A) (hbarK : kbar M.P M.k = K)
      (hsD : sigmaD M.P M.a = D) (hs : sigma M.P M.k = S)
      (hA : Assumption1 M b β γp) (γT γC : ℝ)
      (hT : OptimalTax M b β γp w γT)
      (hC : OptimalCap M b β γp w γC),
      (rho M.P M.a M.k < R0 b β γp A K D S →
        ((γT + γC < A / K → ST M b γT < SC M b γC) ∧
         (¬ (γT + γC < A / K) → SC M b γC ≤ ST M b γT))) ∧
      (R0 b β γp A K D S < rho M.P M.a M.k →
        ((γT + γC < A / K → SC M b γC < ST M b γT) ∧
         (¬ (γT + γC < A / K) → ST M b γT ≤ SC M b γC)))) := by
  obtain ⟨hR, hRpos, hR0pos, hord, R1, R2, hiff⟩ :=
    CarbonCor1Aux.pure_main b β γp A K D S hb hγp hK hD hS hcurvature hinvestment hdemand
  have hR1 : R1 < R b β γp A K D S := ((hiff _).mp hRpos).1
  have hR2 : R0 b β γp A K D S < R2 := ((hiff _).mp hR0pos).2
  refine ⟨⟨R1, R2, hR1, hR, hR2, ?_⟩, ?_⟩
  · intro Ω _ M hbarA hbarK hsD hs hA γT γC hT hC
    have hγT := (lemma_1 M b β γp w hb hγp hA).2 γT hT
    have hγC := (lemma_2 M b β γp w hb hγp hA).2 γC hC
    rw [hbarA, hbarK] at hγT
    rw [hbarA, hbarK, hsD, hs] at hγC
    rw [CarbonCor1Aux.CST_eq M b β γp γT hb, CarbonCor1Aux.CSC_eq M b β γp γC hb,
      hbarA, hbarK, hsD, hs, div_lt_div_iff_of_pos_right (by positivity), ← hiff]
    unfold CarbonCor1Aux.dCS
    rw [← hγT, ← hγC]
    have e : ((A - γT * K) ^ 2 + D ^ 2) - ((A - γC * K) ^ 2 + D ^ 2 +
        (γC ^ 2 * S ^ 2 - 2 * γC * rho M.P M.a M.k * D * S)) =
        (A - γT * K) ^ 2 - (A - γC * K) ^ 2 - γC ^ 2 * S ^ 2
          + 2 * γC * (rho M.P M.a M.k * D * S) := by ring
    constructor <;> intro h <;> linarith
  · intro Ω _ M hbarA hbarK hsD hs hA γT γC hT hC
    have hγT := (lemma_1 M b β γp w hb hγp hA).2 γT hT
    have hγC := (lemma_2 M b β γp w hb hγp hA).2 γC hC
    rw [hbarA, hbarK] at hγT
    rw [hbarA, hbarK, hsD, hs] at hγC
    have hED := emission_difference M b γT γC hb
    rw [hbarA, hbarK] at hED
    have h2b : 0 < 2 * b := by linarith
    have hsplit : ∀ x : ℝ, (x < A / K ↔ x * K < A) := fun x => lt_div_iff₀ hK
    constructor
    · intro hlt
      have hTC : γT < γC := by rw [hγT, hγC]; exact (hord _).1 hlt
      constructor
      · intro h
        rw [hsplit] at h
        have : (γT - γC) * (A - (γT + γC) * K) / (2 * b) < 0 :=
          div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) h2b
        linarith
      · intro h
        rw [hsplit] at h
        have : 0 ≤ (γT - γC) * (A - (γT + γC) * K) / (2 * b) :=
          div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) h2b.le
        linarith
    · intro hgt
      have hCT : γC < γT := by rw [hγT, hγC]; exact (hord _).2 hgt
      constructor
      · intro h
        rw [hsplit] at h
        have : 0 < (γT - γC) * (A - (γT + γC) * K) / (2 * b) :=
          div_pos (mul_pos (by linarith) (by linarith)) h2b
        linarith
      · intro h
        rw [hsplit] at h
        have : (γT - γC) * (A - (γT + γC) * K) / (2 * b) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) h2b.le
        linarith
