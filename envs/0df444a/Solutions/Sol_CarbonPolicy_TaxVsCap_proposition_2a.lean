-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.proposition_2a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T21:44:52.97698+00:00
-- url     : https://prove2.me/submissions/531c0f63-e951-4015-baf3-193134f871e5

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
import Theorems.Thm_CarbonPolicy_TaxVsCap_moment_tax
import Theorems.Thm_CarbonPolicy_TaxVsCap_moment_cap
import Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_1
import Theorems.Thm_CarbonPolicy_TaxVsCap_lemma_2

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
theorem pure_2a (b β γp A K D S : ℝ)
    (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K)
    (hD : 0 < D) (hS : 0 < S)
    (hcurvature : K ^ 2 + S ^ 2 < 4 * b * β)
    (hinvestment : A * K < 4 * b * β * γp)
    (hdemand : γp * K < A) :
    0 < R b β γp A K D S ∧ R b β γp A K D S < R0 b β γp A K D S ∧
    ∀ ρ : ℝ, A * K + ρ * D * S < 4 * b * β * γp →
      (0 < dCS b β γp A K D S ρ - 4 * b * β * ((γp - gammaT0 b β γp A K) ^ 2 -
          (γp - gammaC0 b β γp A K D S ρ) ^ 2) ↔ R b β γp A K D S < ρ) := by
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
  have hdPi : ∀ ρ : ℝ, dCS b β γp A K D S ρ - 4 * b * β * ((γp - gT) ^ 2 -
      (γp - gammaC0 b β γp A K D S ρ) ^ 2)
      = gT ^ 2 * E - (2 * (N - ρ * P) * gammaC0 b β γp A K D S ρ
          - Dp * (gammaC0 b β γp A K D S ρ) ^ 2) := by
    intro ρ; rw [hdCS]; ring
  have hNP : ∀ ρ : ℝ, A * K + ρ * D * S < 4 * b * β * γp → ρ * P < N := by
    intro ρ h; rw [hPdef, hNdef]; linarith
  have hr0N : 0 < N - r0 * P := by linarith
  have hDE : 0 < Dp * E := by positivity
  have hiffP : ∀ x y : ℝ, x < y ↔ x * P < y * P := fun x y => (mul_lt_mul_iff_left₀ hP).symm
  by_cases h0 : rho0 b β γp A K D S > rhoC γp A K D S
  · have hR : R b β γp A K D S = r0 := by unfold R; rw [if_pos h0]
    have hin : (4 * b * β * γp - A * K) - Dp * γp < r0 * P := by
      rw [← hrhoC]; exact (mul_lt_mul_iff_left₀ hP).mpr h0
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
    have hr0pos : 0 < r0 := by
      have h1 : (N - r0 * P) ^ 2 * E < N ^ 2 * E := by
        rw [hsq]
        exact mul_lt_mul_of_pos_left (by rw [hDpE]; linarith [sq_pos_of_pos hS]) (by positivity)
      have h2 : (N - r0 * P) ^ 2 < N ^ 2 := lt_of_mul_lt_mul_right h1 hE.le
      have h3 : N - r0 * P < N := lt_of_pow_lt_pow_left₀ 2 hN.le h2
      by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonpos_of_nonneg hc hP.le
      linarith
    have hstrict : gT ^ 2 * E < Dp * γp ^ 2 := by
      have h1 : (N - r0 * P) ^ 2 < (Dp * γp) ^ 2 :=
        pow_lt_pow_left₀ (by linarith) hr0N.le two_ne_zero
      have h2 := mul_lt_mul_of_pos_right h1 hE
      have h3 : N ^ 2 * Dp = gT ^ 2 * E ^ 2 * Dp := by rw [← hgT]; ring
      have h4 : (gT ^ 2 * E) * (Dp * E) < (Dp * γp ^ 2) * (Dp * E) := by linarith
      exact lt_of_mul_lt_mul_right h4 hDE.le
    refine ⟨by rw [hR]; exact hr0pos, by rw [hR, ← mul_lt_mul_iff_left₀ hP, hR0]; exact hlt, ?_⟩
    intro ρ hρ
    have hρN := hNP ρ hρ
    rw [hdPi, hR, hiffP r0 ρ]
    by_cases hin' : (4 * b * β * γp - A * K) - Dp * γp < ρ * P
    · have hg' := hint ρ hin'
      set g := gammaC0 b β γp A K D S ρ with hgdef
      have key : (gT ^ 2 * E - (2 * (N - ρ * P) * g - Dp * g ^ 2)) * (Dp * E)
          = ((N - r0 * P) ^ 2 - (N - ρ * P) ^ 2) * E := by
        rw [← hg']
        linear_combination (gT * E + N) * Dp * hgT - hsq
      constructor
      · intro h
        by_contra hc; push_neg at hc
        have h1 : (N - r0 * P) ^ 2 ≤ (N - ρ * P) ^ 2 :=
          pow_le_pow_left₀ hr0N.le (by linarith) 2
        have h2 := mul_pos h hDE
        rw [key] at h2
        have h3 := mul_le_mul_of_nonneg_right h1 hE.le
        linarith
      · intro h
        have h1 : (N - ρ * P) ^ 2 < (N - r0 * P) ^ 2 :=
          pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
        have h2 := mul_lt_mul_of_pos_right h1 hE
        by_contra hc; push_neg at hc
        have h3 := mul_nonpos_of_nonpos_of_nonneg hc hDE.le
        rw [key] at h3
        linarith
    · push_neg at hin'
      rw [hcor ρ hin']
      constructor
      · intro h
        exfalso
        have h1 : Dp * γp * (2 * γp) ≤ (N - ρ * P) * (2 * γp) :=
          mul_le_mul_of_nonneg_right (by rw [hNdef]; linarith) (by linarith)
        linarith
      · intro h
        exfalso
        linarith
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
    have h3N : N ^ 2 = gT ^ 2 * E ^ 2 := by rw [← hgT]; ring
    have hc1 : c1 ≤ (4 * b * β * γp - A * K) - Dp * γp := by
      have h1 : c1 * (2 * γp * E) ≤ ((4 * b * β * γp - A * K) - Dp * γp) * (2 * γp * E) := by
        rw [hrho1, ← hNdef]
        linarith [mul_le_mul_of_nonneg_right hineq hE.le]
      exact le_of_mul_le_mul_right h1 (by positivity)
    have hz : gT ^ 2 * E - (2 * (N - c1) * γp - Dp * γp ^ 2) = 0 := by
      have h1 : (gT ^ 2 * E - (2 * (N - c1) * γp - Dp * γp ^ 2)) * E = 0 := by
        linear_combination hrho1 - h3N
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hE.ne'
    have hc1pos : 0 < c1 := by
      by_contra hc; push_neg at hc
      have h1 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity : (0:ℝ) ≤ 2 * γp * E)
      rw [hrho1] at h1
      have hN2 : N * γp * E = gT * E * γp * E := by rw [← hgT]
      have hpos : 0 < gT * E ^ 2 * (γp - gT) :=
        mul_pos (mul_pos hgTpos (pow_pos hE 2)) (sub_pos.mpr hgTlt)
      linarith [mul_le_mul_of_nonneg_right hineq hE.le]
    have hrho1pos : 0 < rho1 b β γp A K D S := by
      by_contra hc; push_neg at hc
      have := mul_nonpos_of_nonpos_of_nonneg hc hP.le
      linarith
    refine ⟨by rw [hR]; exact hrho1pos, ?_, ?_⟩
    · rw [hR, ← mul_lt_mul_iff_left₀ hP, hR0]
      have := mul_lt_mul_of_pos_left hgTlt hDp
      linarith
    intro ρ hρ
    have hρN := hNP ρ hρ
    rw [hdPi, hR, hiffP (rho1 b β γp A K D S) ρ]
    by_cases hin' : (4 * b * β * γp - A * K) - Dp * γp < ρ * P
    · have hg' := hint ρ hin'
      set g := gammaC0 b β γp A K D S ρ with hgdef
      have hgl : g < γp := by
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hDp.le
        linarith
      have hg0 : 0 < g := by
        by_contra hc; push_neg at hc
        have := mul_nonpos_of_nonpos_of_nonneg hc hDp.le
        linarith
      have hsqlt : g ^ 2 < γp ^ 2 := pow_lt_pow_left₀ hgl hg0.le two_ne_zero
      have := mul_lt_mul_of_pos_left hsqlt hDp
      refine iff_of_true ?_ (by linarith)
      rw [← hg']
      linarith
    · push_neg at hin'
      rw [hcor ρ hin']
      have hX : gT ^ 2 * E - (2 * (N - ρ * P) * γp - Dp * γp ^ 2) = 2 * γp * (ρ * P - c1) := by
        linarith
      rw [hX, mul_pos_iff_of_pos_left (by linarith : (0:ℝ) < 2 * γp), sub_pos]

lemma int_demand {Ω : Type} [MeasurableSpace Ω] (M : Model Ω) (γp : ℝ)
    (hae : ∀ᵐ ω ∂M.P, γp * M.k ω < M.a ω) :
    γp * kbar M.P M.k < abar M.P M.a := by
  haveI := M.prob
  have hia : Integrable M.a M.P := M.a_L2.integrable one_le_two
  have hik : Integrable M.k M.P := M.k_L2.integrable one_le_two
  have hf : Integrable (fun ω => M.a ω - γp * M.k ω) M.P := hia.sub (hik.const_mul γp)
  have heq : ∫ ω, (M.a ω - γp * M.k ω) ∂M.P = abar M.P M.a - γp * kbar M.P M.k := by
    unfold abar kbar; rw [integral_sub hia (hik.const_mul γp), integral_const_mul]
  have hpos : 0 < ∫ ω, (M.a ω - γp * M.k ω) ∂M.P := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (hae.mono fun ω h => by show (0:ℝ) ≤ M.a ω - γp * M.k ω; linarith) hf]
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := measure_eq_zero_iff_ae_notMem.mp h0
    have h2 : ∀ᵐ ω ∂M.P, False := (hae.and h1).mono fun ω h => h.2 (by
      rw [Function.mem_support]; exact (sub_pos.mpr h.1).ne')
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h2
    exact IsProbabilityMeasure.ne_zero M.P h2
  linarith

end CarbonCor1Aux

open CarbonPolicy.TaxVsCap in
theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp)
    (γT γC : ℝ) (hT : OptimalTax M b β γp w γT)
    (hC : OptimalCap M b β γp w γC) :
    0 < R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) ∧ R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) < R0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) ∧
    (PiC M b β γp w γC < PiT M b β γp w γT ↔
      R b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) < rho M.P M.a M.k) := by
  have hK : 0 < kbar M.P M.k := M.kbar_pos
  have hD : 0 < sigmaD M.P M.a := Real.sqrt_pos.mpr M.var_a_pos
  have hS : 0 < sigma M.P M.k := Real.sqrt_pos.mpr M.var_k_pos
  have hγT := (lemma_1 M b β γp w hb hγp hA).2 γT hT
  have hγC := (lemma_2 M b β γp w hb hγp hA).2 γC hC
  obtain ⟨hcurv, hinv, hae⟩ := hA
  have hinv1 := lt_of_le_of_lt (le_max_left _ _) hinv
  have hinv2 := lt_of_le_of_lt (le_max_right _ _) hinv
  have hdem := CarbonCor1Aux.int_demand M γp hae
  obtain ⟨h1, h2, h3⟩ := CarbonCor1Aux.pure_2a b β γp (abar M.P M.a) (kbar M.P M.k)
    (sigmaD M.P M.a) (sigma M.P M.k) hb hγp hK hD hS (by linarith) hinv1 hdem
  refine ⟨h1, h2, ?_⟩
  rw [← h3 (rho M.P M.a M.k) (by linarith)]
  rw [moment_tax M b β γp w hb γT, moment_cap M b β γp w hb γC]
  unfold CarbonCor1Aux.dCS
  rw [← hγT, ← hγC]
  have e : ((abar M.P M.a - γT * kbar M.P M.k) ^ 2 / (4 * b) + sigmaD M.P M.a ^ 2 / (4 * b) -
        β * (γp - γT) ^ 2 + w * kbar M.P M.k) -
      ((abar M.P M.a - γC * kbar M.P M.k) ^ 2 / (4 * b) + sigmaD M.P M.a ^ 2 / (4 * b) +
        (γC ^ 2 * sigma M.P M.k ^ 2 - 2 * γC * rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k) /
          (4 * b) - β * (γp - γC) ^ 2 + w * kbar M.P M.k) =
      ((abar M.P M.a - γT * kbar M.P M.k) ^ 2 - (abar M.P M.a - γC * kbar M.P M.k) ^ 2 -
        γC ^ 2 * sigma M.P M.k ^ 2 +
        2 * γC * (rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k) -
        4 * b * β * ((γp - γT) ^ 2 - (γp - γC) ^ 2)) / (4 * b) := by
    field_simp; ring
  have h4b : 0 < 4 * b := by linarith
  constructor
  · intro h
    have : 0 < ((abar M.P M.a - γT * kbar M.P M.k) ^ 2 - (abar M.P M.a - γC * kbar M.P M.k) ^ 2 -
        γC ^ 2 * sigma M.P M.k ^ 2 +
        2 * γC * (rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k) -
        4 * b * β * ((γp - γT) ^ 2 - (γp - γC) ^ 2)) / (4 * b) := by linarith
    exact (div_pos_iff_of_pos_right h4b).mp this
  · intro h
    have := div_pos h h4b
    linarith
