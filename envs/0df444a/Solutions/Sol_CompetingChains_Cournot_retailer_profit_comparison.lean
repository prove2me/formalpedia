-- Prove2me | solution 1 for CompetingChains.Cournot.retailer_profit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T10:43:26.450744+00:00
-- url     : https://prove2.me/submissions/d7cb342e-d343-4dec-a9a1-14075b9b8dde

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
open CompetingChains.Cournot
namespace ChainsResearch
lemma denoms (k γ u : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ) (hg1 : γ < 1) (hu : 0 < u) :
    0 < (4*u+4+γ*u)*k-(u+1) ∧
    0 < (8*(u+1)^2-γ^2*u^2)*k-2*(u+1)^2 ∧
    0 < 2*(u+1)+γ*u ∧ 0 < 4*k-1 ∧ 0 < (γ+4)*k-1 := by
  have hk0 : 0 < k := by linarith
  have hg : 0 ≤ γ*u := mul_nonneg hg0 (le_of_lt hu)
  have hgu : γ*u < u := by nlinarith
  have hq : γ^2*u^2 < u^2 := by nlinarith [mul_pos (sub_pos.mpr hgu) (show 0 < u+γ*u by linarith)]
  have hd : 0 < 8*(u+1)^2-γ^2*u^2 := by nlinarith [sq_nonneg (u+1)]
  have hp := mul_pos (show 0 < 3*k-1 by linarith) hd
  have hpk := mul_nonneg (le_of_lt hk0) hg
  have hpγ := mul_nonneg hg0 (le_of_lt hk0)
  refine ⟨?_, ?_, by positivity, by linarith, by nlinarith⟩
  · nlinarith [mul_pos (show 0 < 3*k-1 by linarith) (show 0 < u+1 by linarith)]
  · nlinarith [sq_nonneg u]

lemma coeff_bounds (k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) :
    ∀ Xi Xj, 0 < C k γ t σsq Xi Xj ∧ C k γ t σsq Xi Xj < 1 := by
  have hu : 0 < t*σsq := mul_pos ht hs
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 hu
  have hk0 : 0 < k := by linarith
  have h3 : 0 < 3*k-1 := by linarith
  have hγ : 0 < 1-γ := by linarith
  have hpart := mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hk0) hg0) (sq_nonneg (t*σsq))) (le_of_lt hγ)
  intro Xi Xj
  cases Xi <;> cases Xj <;> simp only [C]
  · constructor
    · exact div_pos (mul_pos hk0 hu) ha
    · apply (div_lt_one ha).mpr
      nlinarith [mul_pos h3 (show 0 < t*σsq+1 by linarith), mul_nonneg (le_of_lt hk0) (mul_nonneg hg0 (le_of_lt hu))]
  · have hB : 0 < (8*(1+t*σsq)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2 := by simpa [add_comm] using hb
    constructor
    · apply div_pos _ hB
      have : 0 < 2-γ := by linarith
      positivity
    · apply (div_lt_one hB).mpr
      nlinarith [mul_pos h3 (sq_pos_of_pos (show 0 < t*σsq+1 by linarith)), mul_pos hk0 (show 0 < t*σsq+1 by linarith)]
  · constructor
    · apply div_pos _ hb
      apply mul_pos _ hu
      nlinarith [mul_pos h3 (show 0 < t*σsq+1 by linarith), mul_pos hk0 (show 0 < 1+(1-γ)*(t*σsq) by positivity)]
    · apply (div_lt_one hb).mpr
      nlinarith [mul_pos hd (mul_pos (show 0 < t*σsq+1 by linarith) (show 0 < t*σsq+2 by linarith))]
  · constructor
    · exact div_pos hu hc
    · apply (div_lt_one hc).mpr
      nlinarith [mul_nonneg hg0 (le_of_lt hu)]
end ChainsResearch

namespace ChainsResearch
lemma coeff_diff (k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) :
    C k γ t σsq .S .S - C k γ t σsq .N .S =
      (t*σsq)*(t*σsq+1)^2*(4*k-1)*(1-2*k) /
      (((4*(t*σsq)+4+γ*(t*σsq))*k-(t*σsq+1))*
       ((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)) ∧
    C k γ t σsq .S .N - C k γ t σsq .N .N =
      2*(t*σsq)*(t*σsq+1)^2*(1-2*k) /
      (((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)*
       (2*(t*σsq+1)+γ*(t*σsq))) := by
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 (mul_pos ht hs)
  have hb' : (8*(1+t*σsq)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2 ≠ 0 := by
    simpa [add_comm] using hb.ne'
  constructor <;> simp only [C] <;>
    field_simp (disch := first | assumption | positivity | nlinarith) [ha.ne',hb.ne',hb',hc.ne'] <;> ring

lemma retailer_identity (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) (Xi Xj : Arrangement) :
    PiR a c k γ t σsq Xi Xj =
      k^2*(a-c)^2/(4*k+k*γ-1)^2 + (C k γ t σsq Xi Xj / sig t σsq)^2 * sigTerm t σsq := by
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 (mul_pos ht hs)
  have hb' : (8*(1+t*σsq)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2 ≠ 0 := by
    simpa [add_comm] using hb.ne'
  have hu : t*σsq ≠ 0 := ne_of_gt (mul_pos ht hs)
  have hcoef : C k γ t σsq Xi Xj / sig t σsq =
      (match Xi with | .S => k/(4*k-1) | .N => 1/2) *
        (1-γ*C k γ t σsq Xj Xi) := by
    cases Xi <;> cases Xj <;> simp only [C,sig] <;>
      field_simp (disch := first | assumption | positivity | nlinarith) [ha.ne',hb.ne',hb',hc.ne',hd.ne',hu] <;> ring
  rw [hcoef]
  cases Xi <;> simp only [PiR,piR,mul_pow,div_pow] <;> ring

lemma retailer (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) (Xj : Arrangement) :
    (k ≤ 1/2 → PiR a c k γ t σsq .N Xj ≤ PiR a c k γ t σsq .S Xj) ∧
    (1/2 < k → PiR a c k γ t σsq .S Xj < PiR a c k γ t σsq .N Xj) := by
  have hu := mul_pos ht hs
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 hu
  have hf := coeff_diff k γ t σsq hk hg0 hg1 ht hs
  have hbds := coeff_bounds k γ t σsq hk hg0 hg1 ht hs
  have hsig : 0 < sig t σsq := by unfold sig; positivity
  have hterm : 0 < sigTerm t σsq := by unfold sigTerm; positivity
  have hdif : (k ≤ 1/2 → C k γ t σsq .N Xj ≤ C k γ t σsq .S Xj) ∧
      (1/2 < k → C k γ t σsq .S Xj < C k γ t σsq .N Xj) := by
    constructor
    · intro h
      have hfac : 0 ≤ 1-2*k := by linarith
      have hnon : 0 ≤ C k γ t σsq .S Xj - C k γ t σsq .N Xj := by
        cases Xj
        · rw [hf.1]; positivity
        · rw [hf.2]; positivity
      linarith
    · intro h
      have hfac : 1-2*k < 0 := by linarith
      have hneg : C k γ t σsq .S Xj - C k γ t σsq .N Xj < 0 := by
        cases Xj
        · rw [hf.1]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hfac) (by positivity)
        · rw [hf.2]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hfac) (by positivity)
      linarith
  rw [retailer_identity a c k γ t σsq hk hg0 hg1 ht hs .N Xj,
    retailer_identity a c k γ t σsq hk hg0 hg1 ht hs .S Xj]
  constructor
  · intro h
    have hS : 0 < C k γ t σsq .S Xj / sig t σsq := div_pos (hbds .S Xj).1 hsig
    have hN : 0 < C k γ t σsq .N Xj / sig t σsq := div_pos (hbds .N Xj).1 hsig
    have hl := (div_le_div_iff_of_pos_right hsig).mpr (hdif.1 h)
    have hsq : (C k γ t σsq .N Xj / sig t σsq)^2 ≤
        (C k γ t σsq .S Xj / sig t σsq)^2 := by nlinarith
    linarith [mul_le_mul_of_nonneg_right hsq hterm.le]
  · intro h
    have hS : 0 < C k γ t σsq .S Xj / sig t σsq := div_pos (hbds .S Xj).1 hsig
    have hN : 0 < C k γ t σsq .N Xj / sig t σsq := div_pos (hbds .N Xj).1 hsig
    have hl := (div_lt_div_iff_of_pos_right hsig).mpr (hdif.2 h)
    nlinarith [mul_pos (show 0 < (C k γ t σsq .N Xj / sig t σsq)^2 -
      (C k γ t σsq .S Xj / sig t σsq)^2 by nlinarith) hterm]
end ChainsResearch


theorem solution (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    (k ≤ 1 / 2 → ∀ Xj : Arrangement, PiR a c k γ t σsq .N Xj ≤ PiR a c k γ t σsq .S Xj) ∧
    (1 / 2 < k → ∀ Xj : Arrangement, PiR a c k γ t σsq .S Xj < PiR a c k γ t σsq .N Xj) := by
  constructor
  · intro h Xj; exact (ChainsResearch.retailer a c k γ t σsq hk hγ0 hγ1 ht hσ Xj).1 h
  · intro h Xj; exact (ChainsResearch.retailer a c k γ t σsq hk hγ0 hγ1 ht hσ Xj).2 h
