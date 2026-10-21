-- Prove2me | solution 1 for CompetingChains.Cournot.proposition_7a
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T10:53:40.162345+00:00
-- url     : https://prove2.me/submissions/104fdebd-b21a-439a-bbbb-bccbad76a3df

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Source model and result: Albert Y. Ha, Quan Tian and Shilu Tong (2017).
-- Platform formulation/qualifications: mikedeng1; statement review: Shuze Chen.
-- Full explicit proofs of all supporting lemmas are included; no open target imports.
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
noncomputable def G (k q : ℝ) : ℝ :=
  k^3*q^4-8*k^3*q^2-2*(4*k-1)*(-6*k+4*k^2+1)
noncomputable def H (k q : ℝ) : ℝ :=
  k*(4*k-1)*q^4-16*k^2*q^2-8*(-6*k+4*k^2+1)
lemma gains (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) :
    V a c k γ t σsq .S = sigTerm t σsq * (4*k-1) * (t*σsq+1)^6 *
      G k (γ*(t*σsq)/(t*σsq+1)) /
      (2*((4*(t*σsq)+4+γ*(t*σsq))*k-(t*σsq+1))^2 *
        ((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)^2) ∧
    V a c k γ t σsq .N = sigTerm t σsq * (t*σsq+1)^6 *
      H k (γ*(t*σsq)/(t*σsq+1)) /
      (2*(2*(t*σsq+1)+γ*(t*σsq))^2 *
        ((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)^2) := by
  have hu := mul_pos ht hs
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 hu
  have hb' : (8*(1+t*σsq)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2 ≠ 0 := by
    simpa [add_comm] using hb.ne'
  have he' : 4*k+k*γ-1 ≠ 0 := by nlinarith
  have hu' : t*σsq+1 ≠ 0 := by positivity
  constructor <;> simp only [V, PiC, piC, piR, piM, C, G, H] <;>
    field_simp (disch := first | assumption | positivity | nlinarith) [ha.ne', hb.ne', hb', hc.ne', hd.ne', he', hu'] <;> ring
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


namespace ChainsThreshold
noncomputable def G (k q : ℝ) : ℝ := k^3*q^4-8*k^3*q^2-2*(4*k-1)*(-6*k+4*k^2+1)
noncomputable def H (k q : ℝ) : ℝ := k*(4*k-1)*q^4-16*k^2*q^2-8*(-6*k+4*k^2+1)
lemma Gnorm (k q : ℝ) (hk : k ≠ 0) :
    G k q / k^3 = q^4-8*q^2-32+56*(1/k)-20*(1/k)^2+2*(1/k)^3 := by
  unfold G
  field_simp
  <;> ring
lemma Hnorm (k q : ℝ) (hk : k ≠ 0) :
    H k q / k^2 = 4*q^4-16*q^2-32+(48-q^4)*(1/k)-8*(1/k)^2 := by
  unfold H
  field_simp
  <;> ring
lemma Gstrict (q : ℝ) : StrictAntiOn (fun k => G k q / k^3) (Set.Ioi (1/2 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : 0 < a := by have := ha; simp only [Set.mem_Ioi] at this; linarith
  have hb0 : 0 < b := lt_trans ha0 hab
  have hia : 1/a < (2 : ℝ) := (div_lt_iff₀ ha0).mpr (by have := ha; simp only [Set.mem_Ioi] at this; linarith)
  have hib : 1/b < (2 : ℝ) := (div_lt_iff₀ hb0).mpr (by have := hb; simp only [Set.mem_Ioi] at this; linarith)
  have hd : 0 < 1/a-1/b := sub_pos.mpr (one_div_lt_one_div_of_lt ha0 hab)
  have hua : 0 < 2-1/a := sub_pos.mpr hia
  have hub : 0 < 2-1/b := sub_pos.mpr hib
  have hp : 0 < 56-20*(1/a+1/b)+2*((1/a)^2+(1/a)*(1/b)+(1/b)^2) := by
    have he : 56-20*(1/a+1/b)+2*((1/a)^2+(1/a)*(1/b)+(1/b)^2) =
        2*(2-1/a)^2+2*(2-1/b)^2+2*(2-1/a)*(2-1/b)+8*(2-1/a)+8*(2-1/b) := by ring
    rw [he]
    positivity
  change G b q / b^3 < G a q / a^3
  rw [Gnorm a q ha0.ne', Gnorm b q hb0.ne']
  nlinarith [mul_pos hd hp]
lemma Hstrict (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    StrictAntiOn (fun k => H k q / k^2) (Set.Ioi (1/2 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : 0 < a := by have := ha; simp only [Set.mem_Ioi] at this; linarith
  have hb0 : 0 < b := lt_trans ha0 hab
  have hia : 1/a < (2 : ℝ) := (div_lt_iff₀ ha0).mpr (by have := ha; simp only [Set.mem_Ioi] at this; linarith)
  have hib : 1/b < (2 : ℝ) := (div_lt_iff₀ hb0).mpr (by have := hb; simp only [Set.mem_Ioi] at this; linarith)
  have hd : 0 < 1/a-1/b := sub_pos.mpr (one_div_lt_one_div_of_lt ha0 hab)
  have hq4 : q^4 < 1 := pow_lt_one₀ hq0 hq1 (by decide)
  have hp : 0 < 48-q^4-8*(1/a+1/b) := by linarith
  change H b q / b^2 < H a q / a^2
  rw [Hnorm a q ha0.ne', Hnorm b q hb0.ne']
  nlinarith [mul_pos hd hp]
lemma roots (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ kN kS : ℝ, 1/2 < kN ∧ kN < kS ∧ kS < (3+Real.sqrt 5)/4 ∧
      H kN q = 0 ∧ G kS q = 0 := by
  let B := (3+Real.sqrt 5)/4
  have hB : (1/2 : ℝ) < B := by dsimp [B]; nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hB0 : 0 < B := by linarith
  have hquad : -6*B+4*B^2+1 = 0 := by
    dsimp [B]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hq2 : q^2 < 1 := pow_lt_one₀ hq0.le hq1 (by decide)
  have hn : q^2-4 ≠ 0 := by linarith
  have hG0 : 0 < G (1/2) q := by
    have he : G (1/2) q = (q^2-4)^2/8 := by unfold G; ring
    rw [he]
    exact div_pos (sq_pos_of_ne_zero hn) (by norm_num)
  have hH0 : 0 < H (1/2) q := by
    have he : H (1/2) q = (q^2-4)^2/2 := by unfold H; ring
    rw [he]
    exact div_pos (sq_pos_of_ne_zero hn) (by norm_num)
  have hGB : G B q < 0 := by
    have he : G B q = B^3*q^2*(q^2-8) := by unfold G; rw [hquad]; ring
    rw [he]
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos hB0 3) (sq_pos_of_pos hq0)) (by linarith)
  have hHB : H B q < 0 := by
    have he : H B q = B*q^2*((4*B-1)*q^2-16*B) := by unfold H; rw [hquad]; ring
    rw [he]
    apply mul_neg_of_pos_of_neg (mul_pos hB0 (sq_pos_of_pos hq0))
    nlinarith [mul_pos (show 0 < 4*B-1 by linarith) (sub_pos.mpr hq2)]
  have hGc : Continuous (fun k => G k q) := by unfold G; fun_prop
  have hHc : Continuous (fun k => H k q) := by unfold H; fun_prop
  obtain ⟨kS,hkS,hS⟩ := intermediate_value_Icc' hB.le hGc.continuousOn ⟨hGB.le,hG0.le⟩
  obtain ⟨kN,hkN,hN⟩ := intermediate_value_Icc' hB.le hHc.continuousOn ⟨hHB.le,hH0.le⟩
  change G kS q = 0 at hS
  change H kN q = 0 at hN
  have hS0 : (1/2 : ℝ) < kS := by
    by_contra h
    have he : kS=1/2 := by linarith [hkS.1]
    subst kS
    linarith
  have hN0 : (1/2 : ℝ) < kN := by
    by_contra h
    have he : kN=1/2 := by linarith [hkN.1]
    subst kN
    linarith
  have hSB : kS < B := by
    by_contra h
    have he : kS=B := by linarith [hkS.2]
    subst kS
    linarith
  have hNpos : 0 < kN := by linarith
  have hfac : 0 < 4*kN-(6*kN-1)*q^2/4 := by
    nlinarith [mul_pos (show 0 < 6*kN-1 by linarith) (sub_pos.mpr hq2)]
  have h2N : 0 < 2*kN-1 := by linarith
  have hGN : 0 < G kN q := by
    have he : G kN q - (4*kN-1)/4*H kN q =
        kN*(2*kN-1)*q^2*(4*kN-(6*kN-1)*q^2/4) := by unfold G H; ring
    rw [hN] at he
    have hp : 0 < kN*(2*kN-1)*q^2*(4*kN-(6*kN-1)*q^2/4) := by positivity
    nlinarith
  have hNS : kN < kS := by
    by_contra h
    have hle := (Gstrict q).antitoneOn hS0 hN0 (le_of_not_gt h)
    rw [hS, zero_div] at hle
    have hp := div_pos hGN (pow_pos hNpos 3)
    linarith
  exact ⟨kN,kS,hN0,hNS,hSB,hN,hS⟩
lemma signs (F : ℝ → ℝ) (d : ℕ)
    (ha : StrictAntiOn (fun k => F k / k^d) (Set.Ioi (1/2 : ℝ)))
    (r : ℝ) (hr : 1/2 < r) (hroot : F r = 0) (k : ℝ) (hk : 1/2 < k) :
    (0 < F k ↔ k < r) ∧ (F k < 0 ↔ r < k) := by
  have hk0 : 0 < k := by linarith
  have hzero : F r/r^d = 0 := by rw [hroot,zero_div]
  constructor
  · rw [← div_pos_iff_of_pos_right (pow_pos hk0 d)]
    constructor
    · intro hp
      by_contra h
      have hle := ha.antitoneOn hr hk (le_of_not_gt h)
      rw [hzero] at hle
      linarith
    · intro h
      have hp := ha hk hr h
      change F r/r^d < F k/k^d at hp
      rwa [hzero] at hp
  · have hiff : F k < 0 ↔ F k/k^d < 0 := by
      rw [div_lt_iff₀ (pow_pos hk0 d), zero_mul]
    rw [hiff]
    constructor
    · intro hp
      by_contra h
      have hle := ha.antitoneOn hk hr (le_of_not_gt h)
      rw [hzero] at hle
      linarith
    · intro h
      have hp := ha hr hk h
      change F k/k^d < F r/r^d at hp
      rwa [hzero] at hp
end ChainsThreshold


open CompetingChains.Cournot
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ChainsResearch
lemma manufacturer_gain (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hk2 : k ≤ 1 / 2) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    ∀ Xj : Arrangement, PiM a c k γ t σsq .N Xj < PiM a c k γ t σsq .S Xj := by
  intro Xj
  have hC := (ChainsResearch.coeff_bounds k γ t σsq hk hγ0 hγ1 ht hσ Xj .S).2
  have hmul := mul_le_mul_of_nonneg_left hC.le hγ0
  have hpos : 0 < 1-γ*C k γ t σsq Xj .S := by nlinarith
  have hk0 : 0 < k := by linarith
  have hd : 0 < 4*k-1 := by linarith
  have hsig : 0 < sigTerm t σsq := by unfold sigTerm; positivity
  have hgain : 0 < k/(2*(4*k-1))*(1-γ*C k γ t σsq Xj .S)^2*sigTerm t σsq := by positivity
  simp only [PiM, piM]
  linarith

lemma high_payoff_diff (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hk2 : 1/2 < k)
    (hg0 : 0 ≤ γ) (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) (Xj : Arrangement) :
    payoff a c k γ t σsq .S Xj - payoff a c k γ t σsq .N Xj = V a c k γ t σsq Xj := by
  have hr := (retailer a c k γ t σsq hk hg0 hg1 ht hs Xj).2 hk2
  simp only [payoff, mhat]
  rw [if_pos hr]
  simp only [V, PiC, piC, PiR, PiM]
  ring

lemma low_payoff_gain (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hk2 : k ≤ 1/2)
    (hg0 : 0 ≤ γ) (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) (Xj : Arrangement) :
    payoff a c k γ t σsq .N Xj < payoff a c k γ t σsq .S Xj := by
  have hr := (retailer a c k γ t σsq hk hg0 hg1 ht hs Xj).1 hk2
  simp only [payoff, mhat, if_neg (not_lt.mpr hr), sub_zero]
  exact manufacturer_gain a c k γ t σsq hk hk2 hg0 hg1 ht hs Xj

lemma V_signs (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) :
    (0 < V a c k γ t σsq .S ↔ 0 < ChainsThreshold.G k (γ*(t*σsq)/(t*σsq+1))) ∧
    (V a c k γ t σsq .S < 0 ↔ ChainsThreshold.G k (γ*(t*σsq)/(t*σsq+1)) < 0) ∧
    (0 < V a c k γ t σsq .N ↔ 0 < ChainsThreshold.H k (γ*(t*σsq)/(t*σsq+1))) ∧
    (V a c k γ t σsq .N < 0 ↔ ChainsThreshold.H k (γ*(t*σsq)/(t*σsq+1)) < 0) := by
  have hu := mul_pos ht hs
  obtain ⟨ha,hb,hc,hd,he⟩ := denoms k γ (t*σsq) hk hg0 hg1 hu
  have hsig : 0 < sigTerm t σsq := by unfold sigTerm; positivity
  obtain ⟨hS,hN⟩ := gains a c k γ t σsq hk hg0 hg1 ht hs
  have hdS : 0 < 2*((4*(t*σsq)+4+γ*(t*σsq))*k-(t*σsq+1))^2 *
      ((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)^2 := by positivity
  have hdN : 0 < 2*(2*(t*σsq+1)+γ*(t*σsq))^2 *
      ((8*(t*σsq+1)^2-γ^2*(t*σsq)^2)*k-2*(t*σsq+1)^2)^2 := by positivity
  have hwS : 0 < sigTerm t σsq * (4*k-1)*(t*σsq+1)^6 := by positivity
  have hwN : 0 < sigTerm t σsq * (t*σsq+1)^6 := by positivity
  have negscale (w z den : ℝ) (hw : 0 < w) (hden : 0 < den) : w*z/den < 0 ↔ z < 0 := by
    rw [div_lt_iff₀ hden, zero_mul]
    constructor
    · intro h
      by_contra hn
      have := mul_nonneg hw.le (le_of_not_gt hn)
      linarith
    · exact mul_neg_of_pos_of_neg hw
  rw [hS,hN]
  exact ⟨(div_pos_iff_of_pos_right hdS).trans (mul_pos_iff_of_pos_left hwS),
    negscale _ _ _ hwS hdS,
    (div_pos_iff_of_pos_right hdN).trans (mul_pos_iff_of_pos_left hwN),
    negscale _ _ _ hwN hdN⟩

lemma arrangement_forall (P : Arrangement → Prop) :
    (∀ x, P x) ↔ P .S ∧ P .N := by
  constructor
  · intro h; exact ⟨h .S,h .N⟩
  · intro h x; cases x; exact h.1; exact h.2

lemma nash_low (f : Arrangement → Arrangement → ℝ)
    (hS : f .N .S < f .S .S) (hN : f .N .N < f .S .N) :
    pureNashSet f (fun x y => f y x) = {(.S,.S)} := by
  ext ⟨x,y⟩
  cases x <;> cases y <;>
    simp [pureNashSet, IsPureNash, arrangement_forall, hS.le, hN.le,
      not_le.mpr hS, not_le.mpr hN]

lemma nash_mid (f : Arrangement → Arrangement → ℝ)
    (hS : f .N .S < f .S .S) (hN : f .S .N < f .N .N) :
    pureNashSet f (fun x y => f y x) = {(.S,.S),(.N,.N)} := by
  ext ⟨x,y⟩
  cases x <;> cases y <;>
    simp [pureNashSet, IsPureNash, arrangement_forall, hS.le, hN.le,
      not_le.mpr hS, not_le.mpr hN]

lemma nash_high (f : Arrangement → Arrangement → ℝ)
    (hS : f .S .S < f .N .S) (hN : f .S .N < f .N .N) :
    pureNashSet f (fun x y => f y x) = {(.N,.N)} := by
  ext ⟨x,y⟩
  cases x <;> cases y <;>
    simp [pureNashSet, IsPureNash, arrangement_forall, hS.le, hN.le,
      not_le.mpr hS, not_le.mpr hN]
end ChainsResearch

open ChainsResearch

theorem solution (γ t σsq : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    ∃ kN kS : ℝ, 1 / 2 < kN ∧ kN < kS ∧ kS < (3 + Real.sqrt 5) / 4 ∧
      ∀ a c k : ℝ, Standing a c k γ t σsq →
        (k < kN → equilibria a c k γ t σsq = {(.S, .S)}) ∧
        (kN < k → k < kS →
          equilibria a c k γ t σsq = {(.S, .S), (.N, .N)} ∧
            payoff a c k γ t σsq .N .N < payoff a c k γ t σsq .S .S) ∧
        (kS < k → equilibria a c k γ t σsq = {(.N, .N)}) := by
  let q := γ*(t*σsq)/(t*σsq+1)
  have hu : 0 < t*σsq := mul_pos ht hσ
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_one (by positivity)).mpr
    nlinarith [mul_pos (sub_pos.mpr hγ1) hu]
  obtain ⟨kN,kS,hN,hNS,hS,hHN,hGS⟩ := ChainsThreshold.roots q hq0 hq1
  have hclass (a c k : ℝ) (hk : 1/3 < k) (hk2 : 1/2 < k) :
      (payoff a c k γ t σsq .N .S < payoff a c k γ t σsq .S .S ↔ k < kS) ∧
      (payoff a c k γ t σsq .S .S < payoff a c k γ t σsq .N .S ↔ kS < k) ∧
      (payoff a c k γ t σsq .N .N < payoff a c k γ t σsq .S .N ↔ k < kN) ∧
      (payoff a c k γ t σsq .S .N < payoff a c k γ t σsq .N .N ↔ kN < k) := by
    have hh := ChainsThreshold.signs (fun k => ChainsThreshold.H k q) 2
      (ChainsThreshold.Hstrict q hq0.le hq1) kN hN hHN k hk2
    have hg := ChainsThreshold.signs (fun k => ChainsThreshold.G k q) 3
      (ChainsThreshold.Gstrict q) kS (hN.trans hNS) hGS k hk2
    have hv := V_signs a c k γ t σsq hk hγ0.le hγ1 ht hσ
    have hpS := high_payoff_diff a c k γ t σsq hk hk2 hγ0.le hγ1 ht hσ .S
    have hpN := high_payoff_diff a c k γ t σsq hk hk2 hγ0.le hγ1 ht hσ .N
    refine ⟨?_,?_,?_,?_⟩
    · rw [← sub_pos, hpS]; exact hv.1.trans hg.1
    · rw [← sub_neg, hpS]; exact hv.2.1.trans hg.2
    · rw [← sub_pos, hpN]; exact hv.2.2.1.trans hh.1
    · rw [← sub_neg, hpN]; exact hv.2.2.2.trans hh.2
  refine ⟨kN,kS,hN,hNS,hS,?_⟩
  intro a c k hSt
  have hk : 1/3 < k := hSt.2.2.2.1
  refine ⟨?_,?_,?_⟩
  · intro hkn
    by_cases hk2 : k ≤ 1/2
    · exact nash_low _ (low_payoff_gain a c k γ t σsq hk hk2 hγ0.le hγ1 ht hσ .S)
        (low_payoff_gain a c k γ t σsq hk hk2 hγ0.le hγ1 ht hσ .N)
    · have hc := hclass a c k hk (lt_of_not_ge hk2)
      exact nash_low _ (hc.1.mpr (hkn.trans hNS)) (hc.2.2.1.mpr hkn)
  · intro hkn hks
    have hc := hclass a c k hk (hN.trans hkn)
    have hgain := hc.1.mpr hks
    refine ⟨nash_mid _ hgain (hc.2.2.2.mpr hkn), ?_⟩
    have heq : payoff a c k γ t σsq .N .S = payoff a c k γ t σsq .N .N := rfl
    rwa [heq] at hgain
  · intro hks
    have hc := hclass a c k hk ((hN.trans hNS).trans hks)
    exact nash_high _ (hc.2.1.mpr hks) (hc.2.2.2.mpr (hNS.trans hks))
