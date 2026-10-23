-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T21:33:47.63933+00:00
-- url     : https://prove2.me/submissions/93fc3f40-609a-456a-8544-c54d47fe5015

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

set_option autoImplicit false

open ProbabilityTheory MeasureTheory

namespace CarbonPolicyBD

/-- factorisation of a quadratic that is negative somewhere -/
lemma sign_quad (a2 B C x0 : ℝ) (ha : 0 < a2) (h0 : a2 * x0 ^ 2 + B * x0 + C < 0) :
    ∃ r1 r2 : ℝ, r1 < x0 ∧ x0 < r2 ∧
      ∀ x : ℝ, a2 * x ^ 2 + B * x + C = a2 * ((x - r1) * (x - r2)) := by
  have hΔ : 0 < B ^ 2 - 4 * a2 * C := by nlinarith [sq_nonneg (2 * a2 * x0 + B)]
  set s := Real.sqrt (B ^ 2 - 4 * a2 * C) with hs
  have hs2 : s ^ 2 = B ^ 2 - 4 * a2 * C := Real.sq_sqrt hΔ.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hfac : ∀ x : ℝ, a2 * x ^ 2 + B * x + C =
      a2 * ((x - (-B - s) / (2 * a2)) * (x - (-B + s) / (2 * a2))) := by
    intro x
    have ha' : a2 ≠ 0 := ha.ne'
    have e1 : a2 * ((x - (-B - s) / (2 * a2)) * (x - (-B + s) / (2 * a2))) =
        a2 * x ^ 2 + B * x + (B ^ 2 - s ^ 2) / (4 * a2) := by field_simp; ring
    rw [e1, hs2]; field_simp; ring
  refine ⟨(-B - s) / (2 * a2), (-B + s) / (2 * a2), ?_, ?_, hfac⟩
  · have h1 := hfac x0
    have hle : (-B - s) / (2 * a2) ≤ (-B + s) / (2 * a2) := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have hneg : (x0 - (-B - s) / (2 * a2)) * (x0 - (-B + s) / (2 * a2)) < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    by_contra hc; push_neg at hc; nlinarith
  · have h1 := hfac x0
    have hle : (-B - s) / (2 * a2) ≤ (-B + s) / (2 * a2) := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have hneg : (x0 - (-B - s) / (2 * a2)) * (x0 - (-B + s) / (2 * a2)) < 0 := by
      by_contra hc; push_neg at hc; nlinarith
    by_contra hc; push_neg at hc; nlinarith

/-- the consumer-surplus gap as a function of the unconstrained cap intensity `u` -/
lemma u_interval (Q E N gT γp A K S : ℝ) (hQ : 0 < Q) (hE : 0 < E) (hγp : 0 < γp)
    (hgT0 : 0 < gT) (hgTp : gT < γp)
    (hN : N + A * K = Q * γp) (hSK : S ^ 2 + K ^ 2 = Q - E)
    (hP : (Q + E) * gT ^ 2 + (-2 * Q * γp) * gT + (A ^ 2 - (A - gT * K) ^ 2) < 0) :
    ∃ ulo uhi : ℝ, ulo < gT ∧ ∀ u : ℝ, 0 < u →
      (A ^ 2 - 2 * min u γp * (N - E * u + A * K) + (min u γp) ^ 2 * (S ^ 2 + K ^ 2)
          - (A - gT * K) ^ 2 < 0 ↔ ulo < u ∧ u < uhi) := by
  obtain ⟨r1, r2, hr1, hr2, hfac⟩ := sign_quad (Q + E) (-2 * Q * γp) (A ^ 2 - (A - gT * K) ^ 2)
    gT (by linarith) hP
  set Pp := (Q + E) * γp ^ 2 + (-2 * Q * γp) * γp + (A ^ 2 - (A - gT * K) ^ 2) with hPp
  have hφ1 : ∀ u, u ≤ γp → A ^ 2 - 2 * min u γp * (N - E * u + A * K)
      + (min u γp) ^ 2 * (S ^ 2 + K ^ 2) - (A - gT * K) ^ 2 = (Q + E) * ((u - r1) * (u - r2)) := by
    intro u hu
    rw [min_eq_left hu, ← hfac u]
    linear_combination (-2 * u) * hN + u ^ 2 * hSK
  have hφ2 : ∀ u, γp ≤ u → A ^ 2 - 2 * min u γp * (N - E * u + A * K)
      + (min u γp) ^ 2 * (S ^ 2 + K ^ 2) - (A - gT * K) ^ 2 = Pp + 2 * γp * E * (u - γp) := by
    intro u hu
    rw [min_eq_right hu, hPp]
    linear_combination (-2 * γp) * hN + γp ^ 2 * hSK
  have hPpf : Pp = (Q + E) * ((γp - r1) * (γp - r2)) := hfac γp
  have hQE : 0 < Q + E := by linarith
  by_cases hPp0 : 0 ≤ Pp
  · have hr2p : r2 ≤ γp := by
      by_contra hc; push_neg at hc
      have : (γp - r1) * (γp - r2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith
    refine ⟨r1, r2, hr1, fun u hu => ?_⟩
    rcases le_or_gt u γp with h | h
    · rw [hφ1 u h]
      constructor
      · intro hneg
        have : (u - r1) * (u - r2) < 0 := by
          by_contra hc; push_neg at hc; nlinarith
        constructor
        · by_contra hc; push_neg at hc
          nlinarith
        · by_contra hc; push_neg at hc
          nlinarith
      · rintro ⟨h1, h2⟩
        have : (u - r1) * (u - r2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
        nlinarith
    · rw [hφ2 u h.le]
      constructor
      · intro hneg
        have : 0 < 2 * γp * E * (u - γp) := by
          have := sub_pos.mpr h; positivity
        linarith
      · rintro ⟨_, h2⟩; linarith
  · push_neg at hPp0
    have hr2p : γp < r2 := by
      by_contra hc; push_neg at hc
      have : 0 ≤ (γp - r1) * (γp - r2) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    refine ⟨r1, γp - Pp / (2 * γp * E), hr1, fun u hu => ?_⟩
    have hpos : 0 < 2 * γp * E := by positivity
    rcases le_or_gt u γp with h | h
    · rw [hφ1 u h]
      have hb2 : u < γp - Pp / (2 * γp * E) := by
        have : 0 < -Pp / (2 * γp * E) := div_pos (by linarith) hpos
        rw [neg_div] at this; linarith
      constructor
      · intro hneg
        refine ⟨?_, hb2⟩
        by_contra hc; push_neg at hc
        have : 0 ≤ (u - r1) * (u - r2) := mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (by linarith)
        nlinarith
      · rintro ⟨h1, _⟩
        have : (u - r1) * (u - r2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
        nlinarith
    · rw [hφ2 u h.le]
      have hkey : Pp + 2 * γp * E * (u - γp) < 0 ↔ u < γp - Pp / (2 * γp * E) := by
        have e : (u - (γp - Pp / (2 * γp * E))) * (2 * γp * E) = Pp + 2 * γp * E * (u - γp) := by
          field_simp; ring
        rw [← e]
        constructor
        · intro hh; nlinarith
        · intro hh; nlinarith
      rw [hkey]
      constructor
      · intro h2; exact ⟨by linarith, h2⟩
      · rintro ⟨_, h2⟩; exact h2

lemma case1 (Q E Dd N gT γp A K S u0 : ℝ) (hQ : 0 < Q) (hE : 0 < E) (hS : 0 < S)
    (hgT0 : 0 < gT) (hgTp : gT < γp)
    (hEd : E = Q - K ^ 2 - S ^ 2) (hDd : Dd = Q - K ^ 2) (hN : N = Q * γp - A * K)
    (hgT : gT * Dd = N) (hu0pos : 0 < u0) (hu0sq : E * u0 ^ 2 = Dd * gT ^ 2) (hu0p : u0 < γp) :
    gT < u0 ∧ A ^ 2 - 2 * min u0 γp * (N - E * u0 + A * K) + (min u0 γp) ^ 2 * (S ^ 2 + K ^ 2)
      - (A - gT * K) ^ 2 < 0 := by
  subst hEd hDd hN
  have hg : gT < u0 := by
    by_contra hc; push_neg at hc
    have h1 : u0 ^ 2 ≤ gT ^ 2 := by nlinarith
    nlinarith [sq_nonneg gT, mul_pos hS hS, mul_pos (mul_pos hS hS) (mul_pos hgT0 hgT0)]
  refine ⟨hg, ?_⟩
  rw [min_eq_left hu0p.le]
  have e : A ^ 2 - 2 * u0 * (Q * γp - A * K - (Q - K ^ 2 - S ^ 2) * u0 + A * K) +
      u0 ^ 2 * (S ^ 2 + K ^ 2) - (A - gT * K) ^ 2 = Q * ((u0 - γp) ^ 2 - (gT - γp) ^ 2) := by
    linear_combination hu0sq + (2 * gT) * hgT
  rw [e]
  have : (u0 - γp) ^ 2 - (gT - γp) ^ 2 < 0 := by nlinarith
  nlinarith

lemma case2 (Q E Dd N gT γp A K S u0 c1 : ℝ) (hQ : 0 < Q) (hE : 0 < E) (hDd0 : 0 < Dd)
    (hγp : 0 < γp) (hK : 0 < K) (hA : K * γp < A) (hgTp : gT < γp)
    (hEd : E = Q - K ^ 2 - S ^ 2) (hDd : Dd = Q - K ^ 2) (hN : N = Q * γp - A * K)
    (hgT : gT = N / Dd) (hu0sq : E * u0 ^ 2 = Dd * gT ^ 2) (hu0p : γp ≤ u0)
    (hc1 : c1 = (A * K ^ 2 * (2 * K * γp - A) + (Q * S ^ 2 - S ^ 2 * K ^ 2 - K ^ 4) * γp ^ 2)
      / (2 * Dd * γp)) :
    gT < (N - c1) / E ∧ A ^ 2 - 2 * min ((N - c1) / E) γp * (N - E * ((N - c1) / E) + A * K)
      + (min ((N - c1) / E) γp) ^ 2 * (S ^ 2 + K ^ 2) - (A - gT * K) ^ 2 < 0 := by
  have hDdne : Dd ≠ 0 := hDd0.ne'
  have hNsq : N ^ 2 = Dd * (E * u0 ^ 2) := by
    rw [hu0sq, hgT]; field_simp
  have hid : (N - E * γp - c1) * (2 * Dd * γp) = N ^ 2 - Dd * E * γp ^ 2 := by
    have : Q - K ^ 2 ≠ 0 := by rw [← hDd]; exact hDdne
    rw [hc1, hN, hDd, hEd]; field_simp; ring
  have hge : 0 ≤ N - E * γp - c1 := by
    have h1 : 0 ≤ N ^ 2 - Dd * E * γp ^ 2 := by
      rw [hNsq]
      have : γp ^ 2 ≤ u0 ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (mul_pos hDd0 hE).le
      nlinarith
    rw [← hid] at h1
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  have hu1 : γp ≤ (N - c1) / E := by rw [le_div_iff₀ hE]; linarith
  refine ⟨lt_of_lt_of_le hgTp hu1, ?_⟩
  rw [min_eq_right hu1]
  have e1 : N - E * ((N - c1) / E) = c1 := by field_simp; ring
  rw [e1]
  have e2 : A ^ 2 - 2 * γp * (c1 + A * K) + γp ^ 2 * (S ^ 2 + K ^ 2) - (A - gT * K) ^ 2
      = -((A - K * γp) ^ 2 * Q * K ^ 2) / Dd ^ 2 := by
    rw [hc1, hgT, hN, hDd]
    have : Q - K ^ 2 ≠ 0 := by rw [← hDd]; exact hDdne
    field_simp; ring
  rw [e2]
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : 0 < (A - K * γp) ^ 2 := by have := sub_pos.mpr hA; positivity
  have : 0 < (A - K * γp) ^ 2 * Q * K ^ 2 := by positivity
  linarith

open CarbonPolicy.TaxVsCap in
lemma rho0_spec (b β γp A K D S : ℝ) (hD : 0 < D) (hS : 0 < S)
    (hcurv : K ^ 2 + S ^ 2 < 4 * b * β) (hinv : A * K < 4 * b * β * γp)
    (hgT0 : 0 < gammaT0 b β γp A K) :
    rho0 b β γp A K D S < (4 * b * β * γp - A * K) / (D * S) ∧
    R0 b β γp A K D S + D * S * (rho0 b β γp A K D S) ^ 2 / (4 * b * β * γp - A * K)
      - 2 * rho0 b β γp A K D S = 0 := by
  have hex : ∃ r : ℝ, r < (4 * b * β * γp - A * K) / (D * S) ∧
      R0 b β γp A K D S + D * S * r ^ 2 / (4 * b * β * γp - A * K) - 2 * r = 0 := by
    obtain ⟨g, hg_def⟩ : ∃ g, g = gammaT0 b β γp A K := ⟨_, rfl⟩
    have hR0 : R0 b β γp A K D S = S / D * g := by rw [hg_def]; rfl
    have hDd : 0 < 4 * b * β - K ^ 2 := by nlinarith [sq_nonneg S]
    have hE : 0 < 4 * b * β - K ^ 2 - S ^ 2 := by linarith
    have hN : 0 < 4 * b * β * γp - A * K := by linarith
    have hg : g * (4 * b * β - K ^ 2) = 4 * b * β * γp - A * K := by
      rw [hg_def]; unfold gammaT0; field_simp
    have hg0 : 0 < g := by rw [hg_def]; exact hgT0
    obtain ⟨t, ht_def⟩ : ∃ t, t = Real.sqrt ((4 * b * β - K ^ 2) * (4 * b * β - K ^ 2 - S ^ 2)) :=
      ⟨_, rfl⟩
    have ht2 : t ^ 2 = (4 * b * β - K ^ 2) * (4 * b * β - K ^ 2 - S ^ 2) := by
      rw [ht_def]; exact Real.sq_sqrt (by positivity)
    have ht0 : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.2 (by positivity)
    refine ⟨(4 * b * β * γp - A * K - g * t) / (D * S), ?_, ?_⟩
    · apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith [mul_pos hg0 ht0]
    · have hc : (4 * b * β * γp - A * K - g * t) ^ 2
          - 2 * (4 * b * β * γp - A * K) * (4 * b * β * γp - A * K - g * t)
          + S ^ 2 * g * (4 * b * β * γp - A * K) = 0 := by
        linear_combination g ^ 2 * ht2 + (g * (4 * b * β - K ^ 2) + (4 * b * β * γp - A * K)
          - S ^ 2 * g) * hg
      have e : R0 b β γp A K D S + D * S * ((4 * b * β * γp - A * K - g * t) / (D * S)) ^ 2
            / (4 * b * β * γp - A * K) - 2 * ((4 * b * β * γp - A * K - g * t) / (D * S))
          = ((4 * b * β * γp - A * K - g * t) ^ 2
          - 2 * (4 * b * β * γp - A * K) * (4 * b * β * γp - A * K - g * t)
          + S ^ 2 * g * (4 * b * β * γp - A * K)) / (D * S * (4 * b * β * γp - A * K)) := by
        rw [hR0]; field_simp; ring
      rw [e, hc, zero_div]
  unfold rho0
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma assemble (N E P S g ulo uhi R0v Rv : ℝ) (Φ : ℝ → Prop) (hE : 0 < E) (hP : 0 < P)
    (hR0v : R0v * P = S ^ 2 * g) (hEg : E * g = N - S ^ 2 * g)
    (hlo : ulo < g) (hgu : g < (N - Rv * P) / E) (huR : (N - Rv * P) / E < uhi)
    (hiff : ∀ u : ℝ, 0 < u → (Φ u ↔ ulo < u ∧ u < uhi)) :
    ∃ R1 R2 : ℝ, R1 < Rv ∧ Rv < R0v ∧ R0v < R2 ∧
      ∀ ρ : ℝ, ρ * P < N → (Φ ((N - ρ * P) / E) ↔ R1 < ρ ∧ ρ < R2) := by
  rw [lt_div_iff₀ hE] at hgu
  rw [div_lt_iff₀ hE] at huR
  refine ⟨(N - E * uhi) / P, (N - E * ulo) / P, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hP]; linarith
  · have h1 : Rv * P < R0v * P := by rw [hR0v]; linarith
    exact lt_of_mul_lt_mul_right h1 hP.le
  · rw [lt_div_iff₀ hP, hR0v]
    have : E * ulo < E * g := mul_lt_mul_of_pos_left hlo hE
    linarith
  · intro ρ hρ
    have hu : 0 < (N - ρ * P) / E := div_pos (by linarith) hE
    rw [hiff _ hu]
    have k1 : ulo < (N - ρ * P) / E ↔ ρ < (N - E * ulo) / P := by
      rw [lt_div_iff₀ hE, lt_div_iff₀ hP]; constructor <;> intro hh <;> linarith
    have k2 : (N - ρ * P) / E < uhi ↔ (N - E * uhi) / P < ρ := by
      rw [div_lt_iff₀ hE, div_lt_iff₀ hP]; constructor <;> intro hh <;> linarith
    rw [k1, k2]; exact and_comm

open CarbonPolicy.TaxVsCap in
lemma key_real (b β γp A K D S : ℝ) (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K)
    (hD : 0 < D) (hS : 0 < S)
    (hcurv : K ^ 2 + S ^ 2 < 4 * b * β) (hinv : A * K < 4 * b * β * γp)
    (hdem : γp * K < A) :
    ∃ R1 R2 : ℝ, R1 < R b β γp A K D S ∧ R b β γp A K D S < R0 b β γp A K D S ∧
      R0 b β γp A K D S < R2 ∧
      ∀ ρ g : ℝ, ρ * D * S < 4 * b * β * γp - A * K →
        g = min ((4 * b * β * γp - A * K - ρ * D * S) / (4 * b * β - K ^ 2 - S ^ 2)) γp →
        (A ^ 2 - 2 * g * (ρ * D * S + A * K) + g ^ 2 * (S ^ 2 + K ^ 2)
            < (A - gammaT0 b β γp A K * K) ^ 2 ↔ R1 < ρ ∧ ρ < R2) := by
  have hDd : 0 < 4 * b * β - K ^ 2 := by nlinarith [sq_nonneg S]
  have hE : 0 < 4 * b * β - K ^ 2 - S ^ 2 := by linarith
  have hN : 0 < 4 * b * β * γp - A * K := by linarith
  have hQ : 0 < 4 * b * β := by nlinarith [sq_nonneg S]
  have hDS : 0 < D * S := mul_pos hD hS
  have hgT0' : 0 < gammaT0 b β γp A K := by unfold gammaT0; exact div_pos hN hDd
  obtain ⟨hr0lt, hr0eq⟩ := rho0_spec b β γp A K D S hD hS hcurv hinv hgT0'
  obtain ⟨g, hg_def⟩ : ∃ g, g = gammaT0 b β γp A K := ⟨_, rfl⟩
  have hR0 : R0 b β γp A K D S = S / D * g := by rw [hg_def]; rfl
  rw [← hg_def]
  have hgD : g * (4 * b * β - K ^ 2) = 4 * b * β * γp - A * K := by
    rw [hg_def]; unfold gammaT0; field_simp
  have hg0 : 0 < g := by rw [hg_def]; exact hgT0'
  have hgp : g < γp := by
    rw [hg_def]; unfold gammaT0; rw [div_lt_iff₀ hDd]; nlinarith
  have hP : (4 * b * β + (4 * b * β - K ^ 2 - S ^ 2)) * g ^ 2 + (-2 * (4 * b * β) * γp) * g
      + (A ^ 2 - (A - g * K) ^ 2) < 0 := by
    have e : (4 * b * β + (4 * b * β - K ^ 2 - S ^ 2)) * g ^ 2 + (-2 * (4 * b * β) * γp) * g
      + (A ^ 2 - (A - g * K) ^ 2) = -(S ^ 2 * g ^ 2) := by linear_combination (2 * g) * hgD
    rw [e]; have : 0 < S ^ 2 * g ^ 2 := by positivity
    linarith
  obtain ⟨ulo, uhi, hlo, hiff⟩ := u_interval (4 * b * β) (4 * b * β - K ^ 2 - S ^ 2)
    (4 * b * β * γp - A * K) g γp A K S hQ hE hγp hg0 hgp (by ring) (by ring) hP
  -- facts about rho0
  have hc0 : rho0 b β γp A K D S * D * S < 4 * b * β * γp - A * K := by
    rw [mul_assoc]; exact (lt_div_iff₀ hDS).1 hr0lt
  have hsq0 : S ^ 2 * g * (4 * b * β * γp - A * K) + (rho0 b β γp A K D S * D * S) ^ 2
      - 2 * (rho0 b β γp A K D S * D * S) * (4 * b * β * γp - A * K) = 0 := by
    have e : (D * S * (4 * b * β * γp - A * K)) * (S / D * g + D * S * (rho0 b β γp A K D S) ^ 2
        / (4 * b * β * γp - A * K) - 2 * rho0 b β γp A K D S) =
        S ^ 2 * g * (4 * b * β * γp - A * K) + (rho0 b β γp A K D S * D * S) ^ 2
        - 2 * (rho0 b β γp A K D S * D * S) * (4 * b * β * γp - A * K) := by
      field_simp
    rw [← e, ← hR0, hr0eq, mul_zero]
  have hu0sq : (4 * b * β - K ^ 2 - S ^ 2) *
      ((4 * b * β * γp - A * K - rho0 b β γp A K D S * D * S) / (4 * b * β - K ^ 2 - S ^ 2)) ^ 2
      = (4 * b * β - K ^ 2) * g ^ 2 := by
    have h2 : (4 * b * β * γp - A * K - rho0 b β γp A K D S * D * S) ^ 2 =
        (4 * b * β - K ^ 2) * (4 * b * β - K ^ 2 - S ^ 2) * g ^ 2 := by
      linear_combination hsq0 + (-(4 * b * β * γp - A * K + g * (4 * b * β - K ^ 2)
        - S ^ 2 * g)) * hgD
    rw [div_pow, h2]; field_simp
  have hu0pos : 0 < (4 * b * β * γp - A * K - rho0 b β γp A K D S * D * S) /
      (4 * b * β - K ^ 2 - S ^ 2) := div_pos (by linarith) hE
  have hRf : g < (4 * b * β * γp - A * K - R b β γp A K D S * D * S) / (4 * b * β - K ^ 2 - S ^ 2)
      ∧ A ^ 2 - 2 * min ((4 * b * β * γp - A * K - R b β γp A K D S * D * S) /
          (4 * b * β - K ^ 2 - S ^ 2)) γp *
        (4 * b * β * γp - A * K - (4 * b * β - K ^ 2 - S ^ 2) *
          ((4 * b * β * γp - A * K - R b β γp A K D S * D * S) / (4 * b * β - K ^ 2 - S ^ 2))
          + A * K)
        + (min ((4 * b * β * γp - A * K - R b β γp A K D S * D * S) /
          (4 * b * β - K ^ 2 - S ^ 2)) γp) ^ 2 * (S ^ 2 + K ^ 2) - (A - g * K) ^ 2 < 0 := by
    unfold R
    split_ifs with hcase
    · have hu0p : (4 * b * β * γp - A * K - rho0 b β γp A K D S * D * S) /
          (4 * b * β - K ^ 2 - S ^ 2) < γp := by
        have h1 : ((K ^ 2 + S ^ 2) * γp - A * K) < rho0 b β γp A K D S * D * S := by
          have := hcase; unfold rhoC at this
          rw [gt_iff_lt, div_lt_iff₀ hDS] at this; linarith
        rw [div_lt_iff₀ hE]; nlinarith
      exact case1 (4 * b * β) (4 * b * β - K ^ 2 - S ^ 2) (4 * b * β - K ^ 2)
        (4 * b * β * γp - A * K) g γp A K S _ hQ hE hS hg0 hgp rfl rfl rfl hgD hu0pos hu0sq hu0p
    · have hu0p : γp ≤ (4 * b * β * γp - A * K - rho0 b β γp A K D S * D * S) /
          (4 * b * β - K ^ 2 - S ^ 2) := by
        have h1 : rho0 b β γp A K D S * D * S ≤ ((K ^ 2 + S ^ 2) * γp - A * K) := by
          have := hcase; unfold rhoC at this
          rw [gt_iff_lt, not_lt, le_div_iff₀ hDS] at this; linarith
        rw [le_div_iff₀ hE]; nlinarith
      have hc1 : rho1 b β γp A K D S * D * S = (A * K ^ 2 * (2 * K * γp - A) +
          (4 * b * β * S ^ 2 - S ^ 2 * K ^ 2 - K ^ 4) * γp ^ 2) / (2 * (4 * b * β - K ^ 2) * γp) := by
        unfold rho1; field_simp
      have hA : K * γp < A := by linarith
      exact case2 (4 * b * β) (4 * b * β - K ^ 2 - S ^ 2) (4 * b * β - K ^ 2)
        (4 * b * β * γp - A * K) g γp A K S _ _ hQ hE hDd hγp hK hA hgp rfl rfl rfl
        (by rw [← hgD]; field_simp) hu0sq hu0p hc1
  obtain ⟨hgu, hφ⟩ := hRf
  have huR := (hiff _ (lt_trans hg0 hgu)).1 hφ
  have hEg : (4 * b * β - K ^ 2 - S ^ 2) * g = (4 * b * β * γp - A * K) - S ^ 2 * g := by
    linear_combination hgD
  have hR0' : R0 b β γp A K D S * (D * S) = S ^ 2 * g := by rw [hR0]; field_simp
  rw [mul_assoc (R b β γp A K D S) D S] at hgu huR
  obtain ⟨R1, R2, h1, h2, h3, h4⟩ := assemble (4 * b * β * γp - A * K) (4 * b * β - K ^ 2 - S ^ 2)
    (D * S) S g ulo uhi (R0 b β γp A K D S) (R b β γp A K D S) _ hE hDS hR0' hEg hlo hgu huR.2 hiff
  refine ⟨R1, R2, h1, h2, h3, fun ρ gC hρ hgC => ?_⟩
  rw [mul_assoc ρ D S] at hρ hgC
  have h := h4 ρ hρ
  have e : 4 * b * β * γp - A * K - (4 * b * β - K ^ 2 - S ^ 2) *
      ((4 * b * β * γp - A * K - ρ * (D * S)) / (4 * b * β - K ^ 2 - S ^ 2)) = ρ * (D * S) := by
    field_simp; ring
  rw [e, ← hgC, sub_neg] at h
  rw [mul_assoc ρ D S]; exact h

section model
open CarbonPolicy.TaxVsCap

variable {Ω : Type} [MeasurableSpace Ω]

lemma moments (M : Model Ω) :
    ∫ ω, M.a ω ^ 2 ∂M.P = Var[M.a; M.P] + (abar M.P M.a) ^ 2 ∧
    ∫ ω, M.k ω ^ 2 ∂M.P = Var[M.k; M.P] + (kbar M.P M.k) ^ 2 ∧
    ∫ ω, M.a ω * M.k ω ∂M.P = cov[M.a, M.k; M.P] + abar M.P M.a * kbar M.P M.k := by
  haveI := M.prob
  have h1 := covariance_eq_sub M.a_L2 M.a_L2
  rw [covariance_self M.a_L2.aestronglyMeasurable.aemeasurable] at h1
  have h2 := covariance_eq_sub M.k_L2 M.k_L2
  rw [covariance_self M.k_L2.aestronglyMeasurable.aemeasurable] at h2
  have h3 := covariance_eq_sub M.a_L2 M.k_L2
  simp only [Pi.mul_apply] at h1 h2 h3
  unfold abar kbar
  simp only [sq]
  refine ⟨by linarith, by linarith, by linarith⟩

lemma int_cap (M : Model Ω) (γ : ℝ) :
    ∫ ω, (M.a ω - γ * M.k ω) ^ 2 ∂M.P = (Var[M.a; M.P] + (abar M.P M.a) ^ 2)
      - 2 * γ * (cov[M.a, M.k; M.P] + abar M.P M.a * kbar M.P M.k)
      + γ ^ 2 * (Var[M.k; M.P] + (kbar M.P M.k) ^ 2) := by
  haveI := M.prob
  obtain ⟨m1, m2, m3⟩ := moments M
  have ha2 : Integrable (fun ω => M.a ω ^ 2) M.P := M.a_L2.integrable_sq
  have hk2 : Integrable (fun ω => M.k ω ^ 2) M.P := M.k_L2.integrable_sq
  have hak : Integrable (fun ω => M.a ω * M.k ω) M.P := M.a_L2.integrable_mul M.k_L2
  have e : (fun ω => (M.a ω - γ * M.k ω) ^ 2) =
      fun ω => (M.a ω ^ 2 - (2 * γ) * (M.a ω * M.k ω)) + γ ^ 2 * M.k ω ^ 2 := by
    ext ω; ring
  have i1 : Integrable (fun ω => M.a ω ^ 2 - (2 * γ) * (M.a ω * M.k ω)) M.P :=
    ha2.sub (hak.const_mul _)
  have i2 : Integrable (fun ω => (2 * γ) * (M.a ω * M.k ω)) M.P := hak.const_mul _
  rw [e, integral_add i1 (hk2.const_mul _), integral_sub ha2 i2, integral_const_mul,
    integral_const_mul, m1, m2, m3]

lemma int_tax (M : Model Ω) (c : ℝ) :
    ∫ ω, (M.a ω - c) ^ 2 ∂M.P = Var[M.a; M.P] + (abar M.P M.a - c) ^ 2 := by
  haveI := M.prob
  obtain ⟨m1, -, -⟩ := moments M
  have ha2 : Integrable (fun ω => M.a ω ^ 2) M.P := M.a_L2.integrable_sq
  have ha : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
  have e : (fun ω => (M.a ω - c) ^ 2) =
      fun ω => (M.a ω ^ 2 - (2 * c) * M.a ω) + c ^ 2 := by
    ext ω; ring
  have i1 : Integrable (fun ω => M.a ω ^ 2 - (2 * c) * M.a ω) M.P := ha2.sub (ha.const_mul _)
  have i2 : Integrable (fun ω => (2 * c) * M.a ω) M.P := ha.const_mul _
  rw [e, integral_add i1 (integrable_const _), integral_sub ha2 i2, integral_const_mul,
    integral_const, m1]
  simp only [probReal_univ, one_smul]
  unfold abar; ring

lemma int_lin (M : Model Ω) (u v z : ℝ) :
    ∫ ω, (u * M.a ω + v * M.k ω + z) ∂M.P = u * abar M.P M.a + v * kbar M.P M.k + z := by
  haveI := M.prob
  have ha : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
  have hk : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
  have i1 : Integrable (fun ω => u * M.a ω + v * M.k ω) M.P := (ha.const_mul _).add (hk.const_mul _)
  have i2 : Integrable (fun ω => u * M.a ω) M.P := ha.const_mul _
  have i3 : Integrable (fun ω => v * M.k ω) M.P := hk.const_mul _
  rw [integral_add i1 (integrable_const _), integral_add i2 i3, integral_const_mul,
    integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  unfold abar kbar; ring

lemma profit_eq (b w γ a k : ℝ) (hb : b ≠ 0) :
    profit b w γ a k (qStar b γ a k) = (a - γ * k) ^ 2 / (4 * b) + w * k := by
  unfold profit qStar; field_simp; ring

lemma PiT_eq (M : Model Ω) (b β γp w γ : ℝ) (hb : 0 < b) :
    PiT M b β γp w γ = (Var[M.a; M.P] + (abar M.P M.a - γ * kbar M.P M.k) ^ 2) / (4 * b)
      + w * kbar M.P M.k - β * (γp - γ) ^ 2 := by
  unfold PiT
  simp_rw [profit_eq b w γ _ _ hb.ne']
  have e : (fun ω => (M.a ω - γ * kbar M.P M.k) ^ 2 / (4 * b) + w * kbar M.P M.k) =
      fun ω => (1 / (4 * b)) * (M.a ω - γ * kbar M.P M.k) ^ 2 + w * kbar M.P M.k := by
    ext ω; ring
  haveI := M.prob
  have hi : Integrable (fun ω => (M.a ω - γ * kbar M.P M.k) ^ 2) M.P :=
    (M.a_L2.sub (memLp_const _)).integrable_sq
  rw [e, integral_add (hi.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, int_tax]
  simp only [probReal_univ, one_smul]
  ring

lemma PiC_eq (M : Model Ω) (b β γp w γ : ℝ) (hb : 0 < b) :
    PiC M b β γp w γ = ((Var[M.a; M.P] + (abar M.P M.a) ^ 2)
      - 2 * γ * (cov[M.a, M.k; M.P] + abar M.P M.a * kbar M.P M.k)
      + γ ^ 2 * (Var[M.k; M.P] + (kbar M.P M.k) ^ 2)) / (4 * b)
      + w * kbar M.P M.k - β * (γp - γ) ^ 2 := by
  unfold PiC
  simp_rw [profit_eq b w γ _ _ hb.ne']
  have e : (fun ω => (M.a ω - γ * M.k ω) ^ 2 / (4 * b) + w * M.k ω) =
      fun ω => (1 / (4 * b)) * (M.a ω - γ * M.k ω) ^ 2 + w * M.k ω := by
    ext ω; ring
  haveI := M.prob
  have hi : Integrable (fun ω => (M.a ω - γ * M.k ω) ^ 2) M.P :=
    (M.a_L2.sub (M.k_L2.const_mul γ)).integrable_sq
  have hk : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
  rw [e, integral_add (hi.const_mul _) (hk.const_mul _), integral_const_mul,
    integral_const_mul, int_cap]
  unfold kbar; ring

lemma CST_eq (M : Model Ω) (b γ : ℝ) (hb : 0 < b) :
    CST M b γ = (Var[M.a; M.P] + (abar M.P M.a - γ * kbar M.P M.k) ^ 2) / (8 * b) := by
  unfold CST qStar
  have e : (fun ω => b * ((M.a ω - γ * kbar M.P M.k) / (2 * b)) ^ 2 / 2) =
      fun ω => (1 / (8 * b)) * (M.a ω - γ * kbar M.P M.k) ^ 2 := by
    ext ω; field_simp; ring
  rw [e, integral_const_mul, int_tax]; ring

lemma CSC_eq (M : Model Ω) (b γ : ℝ) (hb : 0 < b) :
    CSC M b γ = ((Var[M.a; M.P] + (abar M.P M.a) ^ 2)
      - 2 * γ * (cov[M.a, M.k; M.P] + abar M.P M.a * kbar M.P M.k)
      + γ ^ 2 * (Var[M.k; M.P] + (kbar M.P M.k) ^ 2)) / (8 * b) := by
  unfold CSC qStar
  have e : (fun ω => b * ((M.a ω - γ * M.k ω) / (2 * b)) ^ 2 / 2) =
      fun ω => (1 / (8 * b)) * (M.a ω - γ * M.k ω) ^ 2 := by
    ext ω; field_simp; ring
  rw [e, integral_const_mul, int_cap]; ring

lemma ST_eq (M : Model Ω) (b γ : ℝ) (hb : 0 < b) :
    CarbonPolicy.TaxVsCap.ST M b γ = γ * (abar M.P M.a - γ * kbar M.P M.k) / (2 * b) := by
  unfold CarbonPolicy.TaxVsCap.ST qStar
  have e : (fun ω => γ * ((M.a ω - γ * kbar M.P M.k) / (2 * b))) =
      fun ω => (γ / (2 * b)) * M.a ω + 0 * M.k ω + (-(γ * γ * kbar M.P M.k / (2 * b))) := by
    ext ω; field_simp; ring
  rw [e, int_lin]; field_simp; ring

lemma SC_eq (M : Model Ω) (b γ : ℝ) (hb : 0 < b) :
    CarbonPolicy.TaxVsCap.SC M b γ = γ * (abar M.P M.a - γ * kbar M.P M.k) / (2 * b) := by
  unfold CarbonPolicy.TaxVsCap.SC qStar
  have e : (fun ω => γ * ((M.a ω - γ * M.k ω) / (2 * b))) =
      fun ω => (γ / (2 * b)) * M.a ω + (-(γ * γ / (2 * b))) * M.k ω + 0 := by
    ext ω; field_simp; ring
  rw [e, int_lin]; field_simp; ring

end model

lemma argmax (f : ℝ → ℝ) (κ v γp γ : ℝ) (hκ : 0 < κ) (hv : 0 < v) (hγp : 0 < γp)
    (hf : ∀ x y, f x - f y = κ * ((y - v) ^ 2 - (x - v) ^ 2))
    (hmax : γ ∈ Set.Icc (0 : ℝ) γp ∧ IsMaxOn f (Set.Icc 0 γp) γ) : γ = min v γp := by
  obtain ⟨⟨h0, h1⟩, hm⟩ := hmax
  have hmem : min v γp ∈ Set.Icc (0 : ℝ) γp := ⟨le_min hv.le hγp.le, min_le_right _ _⟩
  have h2 : f (min v γp) ≤ f γ := hm hmem
  have h3 := hf (min v γp) γ
  have h4 : (γ - v) ^ 2 ≤ (min v γp - v) ^ 2 := by
    by_contra hc; push_neg at hc
    have : 0 < κ * ((γ - v) ^ 2 - (min v γp - v) ^ 2) := mul_pos hκ (by linarith)
    linarith
  rcases le_total v γp with h | h
  · rw [min_eq_left h] at h4 ⊢
    have h5 : (γ - v) ^ 2 = 0 := le_antisymm (by simpa using h4) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h5
    linarith
  · rw [min_eq_right h] at h4 ⊢
    apply le_antisymm h1
    nlinarith

lemma emis (gT gC A K b ST SC : ℝ) (hb : 0 < b) (hK : 0 < K)
    (hST : ST = gT * (A - gT * K) / (2 * b)) (hSC : SC = gC * (A - gC * K) / (2 * b)) :
    (gT < gC → ((gT + gC < A / K → ST < SC) ∧ (¬ (gT + gC < A / K) → SC ≤ ST))) ∧
    (gC < gT → ((gT + gC < A / K → SC < ST) ∧ (¬ (gT + gC < A / K) → ST ≤ SC))) := by
  have hd : ST - SC = (gT - gC) * (A - K * (gT + gC)) / (2 * b) := by
    rw [hST, hSC]; field_simp; ring
  have hsum : gT + gC < A / K ↔ 0 < A - K * (gT + gC) := by
    rw [lt_div_iff₀ hK]; constructor <;> intro h <;> linarith
  have h2b : 0 < 2 * b := by positivity
  refine ⟨fun hlt => ⟨fun hs => ?_, fun hs => ?_⟩, fun hlt => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · have := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.2 hlt) (hsum.1 hs)) h2b
    linarith
  · rw [hsum, not_lt] at hs
    have := div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith : gT - gC ≤ 0) hs) h2b.le
    linarith
  · have := div_pos (mul_pos (sub_pos.2 hlt) (hsum.1 hs)) h2b
    linarith
  · rw [hsum, not_lt] at hs
    have := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ gT - gC) hs) h2b.le
    linarith

open CarbonPolicy.TaxVsCap in
lemma gT_facts (b β γp A K S : ℝ) (hγp : 0 < γp) (hK : 0 < K)
    (hcurv : K ^ 2 + S ^ 2 < 4 * b * β) (hinv : A * K < 4 * b * β * γp) (hdem : γp * K < A) :
    0 < gammaT0 b β γp A K ∧ gammaT0 b β γp A K < γp ∧
    gammaT0 b β γp A K * (4 * b * β - K ^ 2) = 4 * b * β * γp - A * K := by
  have hDd : 0 < 4 * b * β - K ^ 2 := by nlinarith [sq_nonneg S]
  refine ⟨?_, ?_, ?_⟩
  · unfold gammaT0; exact div_pos (by linarith) hDd
  · unfold gammaT0; rw [div_lt_iff₀ hDd]; nlinarith
  · unfold gammaT0; field_simp

open CarbonPolicy.TaxVsCap in
lemma R0_cmp (b β γp A K D S : ℝ) (hγp : 0 < γp) (hK : 0 < K) (hD : 0 < D) (hS : 0 < S)
    (hcurv : K ^ 2 + S ^ 2 < 4 * b * β) (hinv : A * K < 4 * b * β * γp) (hdem : γp * K < A)
    (ρ : ℝ) :
    (ρ < R0 b β γp A K D S → gammaT0 b β γp A K <
      min ((4 * b * β * γp - A * K - ρ * D * S) / (4 * b * β - K ^ 2 - S ^ 2)) γp) ∧
    (R0 b β γp A K D S < ρ →
      min ((4 * b * β * γp - A * K - ρ * D * S) / (4 * b * β - K ^ 2 - S ^ 2)) γp
        < gammaT0 b β γp A K) := by
  obtain ⟨hg0, hgp, hgD⟩ := gT_facts b β γp A K S hγp hK hcurv hinv hdem
  have hE : 0 < 4 * b * β - K ^ 2 - S ^ 2 := by linarith
  have hDS : 0 < D * S := mul_pos hD hS
  have hR0 : R0 b β γp A K D S * (D * S) = S ^ 2 * gammaT0 b β γp A K := by
    unfold R0; field_simp
  have hEg : (4 * b * β - K ^ 2 - S ^ 2) * gammaT0 b β γp A K =
      4 * b * β * γp - A * K - S ^ 2 * gammaT0 b β γp A K := by linear_combination hgD
  constructor
  · intro h
    have h' : ρ * (D * S) < S ^ 2 * gammaT0 b β γp A K := by
      rw [← hR0]; exact mul_lt_mul_of_pos_right h hDS
    apply lt_min _ hgp
    rw [lt_div_iff₀ hE]
    have : ρ * D * S = ρ * (D * S) := by ring
    linarith
  · intro h
    have h' : S ^ 2 * gammaT0 b β γp A K < ρ * (D * S) := by
      rw [← hR0]; exact mul_lt_mul_of_pos_right h hDS
    apply lt_of_le_of_lt (min_le_left _ _)
    rw [div_lt_iff₀ hE]
    have : ρ * D * S = ρ * (D * S) := by ring
    linarith

section model2
open CarbonPolicy.TaxVsCap

lemma model_facts (b β γp w A K D S : ℝ)
    (hb : 0 < b) (hγp : 0 < γp) (hK : 0 < K) (hD : 0 < D) (hS : 0 < S)
    (hcurv : K ^ 2 + S ^ 2 < 4 * b * β) (hinv : A * K < 4 * b * β * γp) (hdem : γp * K < A)
    {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (hbarA : abar M.P M.a = A) (hbarK : kbar M.P M.k = K)
    (hsD : sigmaD M.P M.a = D) (hs : sigma M.P M.k = S)
    (hA : Assumption1 M b β γp) (γT γC : ℝ)
    (hT : OptimalTax M b β γp w γT) (hC : OptimalCap M b β γp w γC) :
    γT = gammaT0 b β γp A K ∧
    rho M.P M.a M.k * D * S < 4 * b * β * γp - A * K ∧
    γC = min ((4 * b * β * γp - A * K - rho M.P M.a M.k * D * S) / (4 * b * β - K ^ 2 - S ^ 2)) γp ∧
    (CSC M b γC < CST M b γT ↔
      A ^ 2 - 2 * γC * (rho M.P M.a M.k * D * S + A * K) + γC ^ 2 * (S ^ 2 + K ^ 2)
        < (A - gammaT0 b β γp A K * K) ^ 2) ∧
    CarbonPolicy.TaxVsCap.ST M b γT = γT * (A - γT * K) / (2 * b) ∧
    CarbonPolicy.TaxVsCap.SC M b γC = γC * (A - γC * K) / (2 * b) := by
  obtain ⟨hg0, hgp, hgD⟩ := gT_facts b β γp A K S hγp hK hcurv hinv hdem
  have hDd : 0 < 4 * b * β - K ^ 2 := by nlinarith [sq_nonneg S]
  have hE : 0 < 4 * b * β - K ^ 2 - S ^ 2 := by linarith
  have hVa : Var[M.a; M.P] = D ^ 2 := by
    rw [← hsD]; unfold sigmaD; rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hVk : Var[M.k; M.P] = S ^ 2 := by
    rw [← hs]; unfold sigma; rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hcov : cov[M.a, M.k; M.P] = rho M.P M.a M.k * D * S := by
    unfold rho; rw [hsD, hs]; field_simp
  have hρ : rho M.P M.a M.k * D * S < 4 * b * β * γp - A * K := by
    have h := hA.2.1
    rw [hbarA, hbarK, hsD, hs] at h
    have := lt_of_le_of_lt (le_max_right _ _) h
    linarith
  have hγT : γT = gammaT0 b β γp A K := by
    have := argmax (PiT M b β γp w) ((4 * b * β - K ^ 2) / (4 * b)) (gammaT0 b β γp A K) γp γT
      (by positivity) hg0 hγp (fun x y => by
        rw [PiT_eq M b β γp w x hb, PiT_eq M b β γp w y hb, hVa, hbarA, hbarK]
        unfold gammaT0; field_simp; ring) hT
    rw [this, min_eq_left hgp.le]
  have hγC : γC = min ((4 * b * β * γp - A * K - rho M.P M.a M.k * D * S) /
      (4 * b * β - K ^ 2 - S ^ 2)) γp := by
    exact argmax (PiC M b β γp w) ((4 * b * β - K ^ 2 - S ^ 2) / (4 * b)) _ γp γC
      (by positivity) (div_pos (by linarith) hE) hγp (fun x y => by
        rw [PiC_eq M b β γp w x hb, PiC_eq M b β γp w y hb, hVa, hVk, hcov, hbarA, hbarK]
        field_simp; ring) hC
  refine ⟨hγT, hρ, hγC, ?_, ?_, ?_⟩
  · rw [CSC_eq M b γC hb, CST_eq M b γT hb, hVa, hVk, hcov, hbarA, hbarK, hγT,
      div_lt_div_iff_of_pos_right (by positivity)]
    constructor <;> intro h <;> linarith
  · rw [ST_eq M b γT hb, hbarA, hbarK]
  · rw [SC_eq M b γC hb, hbarA, hbarK]

end model2

end CarbonPolicyBD

open ProbabilityTheory MeasureTheory CarbonPolicy.TaxVsCap in
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
  obtain ⟨R1, R2, h1, h2, h3, hiff⟩ :=
    CarbonPolicyBD.key_real b β γp A K D S hb hγp hK hD hS hcurvature hinvestment hdemand
  refine ⟨⟨R1, R2, h1, h2, h3, ?_⟩, ?_⟩
  · intro Ω _ M hbarA hbarK hsD hs hA γT γC hT hC
    obtain ⟨-, hρ, hγC, hCS, -, -⟩ := CarbonPolicyBD.model_facts b β γp w A K D S hb hγp hK hD hS
      hcurvature hinvestment hdemand M hbarA hbarK hsD hs hA γT γC hT hC
    rw [hCS]; exact hiff _ _ hρ hγC
  · intro Ω _ M hbarA hbarK hsD hs hA γT γC hT hC
    obtain ⟨hγT, -, hγC, -, hST, hSC⟩ := CarbonPolicyBD.model_facts b β γp w A K D S hb hγp hK hD
      hS hcurvature hinvestment hdemand M hbarA hbarK hsD hs hA γT γC hT hC
    have Em := CarbonPolicyBD.emis γT γC A K b _ _ hb hK hST hSC
    have Cm := CarbonPolicyBD.R0_cmp b β γp A K D S hγp hK hD hS hcurvature hinvestment hdemand
      (rho M.P M.a M.k)
    constructor
    · intro hlt
      apply Em.1
      rw [hγT, hγC]; exact Cm.1 hlt
    · intro hgt
      apply Em.2
      rw [hγT, hγC]; exact Cm.2 hgt
