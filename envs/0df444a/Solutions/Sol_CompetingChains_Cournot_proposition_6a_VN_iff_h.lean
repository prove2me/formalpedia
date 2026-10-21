-- Prove2me | solution 1 for CompetingChains.Cournot.proposition_6a_VN_iff_h
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T09:23:19.695581+00:00
-- url     : https://prove2.me/submissions/8670b3b8-9aa4-430e-bfda-5f853d425c87

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Mathematical model: Albert Y. Ha, Quan Tian and Shilu Tong (2017).
-- Platform formulation and prior qualifications: mikedeng1; review: Shuze Chen.
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
lemma gain_value (a c k γ t σsq : ℝ) (hk : 1/3 < k) (hg0 : 0 ≤ γ)
    (hg1 : γ < 1) (ht : 0 < t) (hs : 0 < σsq) :
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
  simp only [V, PiC, piC, piR, piM, C, G, H]
  field_simp (disch := first | assumption | positivity | nlinarith)
  <;> ring
end ChainsResearch

theorem solution (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    0 < V a c k γ t σsq .N ↔
      0 < k * (4 * k - 1) * (t ^ 4 * σsq ^ 4 * γ ^ 4 / (t * σsq + 1) ^ 4) -
        16 * k ^ 2 * (t ^ 2 * σsq ^ 2 * γ ^ 2 / (t * σsq + 1) ^ 2) -
        8 * (-6 * k + 4 * k ^ 2 + 1) := by
  have hu := mul_pos ht hσ
  obtain ⟨ha,hb,hc,hd,he⟩ := ChainsResearch.denoms k γ (t*σsq) hk hγ0 hγ1 hu
  have hsig : 0 < sigTerm t σsq := by unfold sigTerm; positivity
  rw [ChainsResearch.gain_value a c k γ t σsq hk hγ0 hγ1 ht hσ,
    div_pos_iff_of_pos_right (by positivity), mul_pos_iff_of_pos_left (by positivity)]
  congr 1
  simp only [ChainsResearch.H, div_pow]
  ring

