-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.source_exclusions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:59.163744+00:00
-- url     : https://prove2.me/submissions/36d20581-9e39-4c75-89d8-745327c68915

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions
import Theorems.Thm_ConsistentSubmodular_LowRollback_child_coefficients
import Theorems.Thm_ConsistentSubmodular_LowRollback_SJ_positive

section

set_option maxHeartbeats 1500000

namespace ConsistentSubmodular.LowRollback

private theorem SS_monotone (u v q : ℝ) (huv : u ≤ v) (hv : v ≤ 20 / 11)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : SS v q ≤ SS u q := by
  obtain ⟨hc, ha, ha3, hA⟩ := child_coefficients q hq0 hq1
  have hbound : 0 < SB q - (40 / 11) * SA q := by
    have hi : SB q - (40 / 11) * SA q =
        (3 / 11) * (15 + 123 * (1 - q) + (1 - q) ^ 2 * (13 - 7 * (1 - q))) := by
      unfold SB SA cpoly apoly npoly
      ring
    have hx : 0 ≤ 1 - q := by linarith
    have hy : 0 ≤ 13 - 7 * (1 - q) := by linarith
    rw [hi]
    positivity
  have hm := mul_nonneg hA.le (show 0 ≤ 40 / 11 - (u + v) by linarith)
  have hbr : 0 ≤ SB q - SA q * (u + v) := by linarith
  have heq : SS u q - SS v q = (v - u) * (SB q - SA q * (u + v)) := by
    unfold SS SR SB SA
    ring
  have hp := mul_nonneg (sub_nonneg.mpr huv) hbr
  linarith

private theorem SS_positive_H (k q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hH : 0 ≤ 20 - 11 * k + (2 * k - 5) * q) : 0 < SS k q := by
  let v := 5 * (4 - q) / (11 - 2 * q)
  have hd : 0 < 11 - 2 * q := by linarith
  have hkv : k ≤ v := by apply (le_div_iff₀ hd).mpr; nlinarith
  have hv : v ≤ 20 / 11 := by apply (div_le_iff₀ hd).mpr; nlinarith
  have hm := SS_monotone k v q hkv hv hq0 hq1
  have hpoly : 0 < 144 - 468 * q + 637 * q ^ 2 - 363 * q ^ 3 + 84 * q ^ 4 - 7 * q ^ 5 := by
    have hh : 0 ≤ 1 - q := by linarith
    have hi : 10 * (144 - 468 * q + 637 * q ^ 2 - 363 * q ^ 3 + 84 * q ^ 4 - 7 * q ^ 5) =
        180 + 1260 * (1 - q) ^ 5 + 1620 * q * (1 - q) ^ 4 + 250 * q ^ 2 * (1 - q) ^ 3+
        270 * q ^ 4 * (1 - q) + 90 * q ^ 5 := by ring
    have hr : 0 < 180 + 1260 * (1 - q) ^ 5 + 1620 * q * (1 - q) ^ 4 + 250 * q ^ 2 * (1 - q) ^ 3+
        270 * q ^ 4 * (1 - q) + 90 * q ^ 5 := by positivity
    linarith
  have hi : (11 - 2 * q) ^ 2 * SS v q =
      3 * (144 - 468 * q + 637 * q ^ 2 - 363 * q ^ 3 + 84 * q ^ 4 - 7 * q ^ 5) := by
    dsimp [v, SS, SR, cpoly, npoly, apoly]
    field_simp
    ring
  have hp : 0 < SS v q := by
    apply (mul_pos_iff_of_pos_left (sq_pos_of_pos hd)).mp
    rw [hi]
    linarith
  exact hp.trans_le hm

private theorem SS_positive_small (k q : ℝ) (hk : k ≤ 40 / 23)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < SS k q := by
  have hm := SS_monotone k (40 / 23) q hk (by norm_num) hq0 hq1
  have hx : 0 ≤ 1 - q := by linarith
  have hp : 0 < 1136 * (1 - q) ^ 2 - 285 * (1 - q) + 18 + 427 * (1 - q) ^ 3 := by
    have hc := pow_nonneg hx 3
    nlinarith [sq_nonneg ((1 - q) - 285 / 2272)]
  have hi : SS (40 / 23) q = (3 / 529) * (1136 * (1 - q) ^ 2 - 285 * (1 - q) + 18 + 427 * (1 - q) ^ 3) := by
    unfold SS SR cpoly npoly apoly
    ring
  have hv : 0 < SS (40 / 23) q := by rw [hi]; positivity
  exact hv.trans_le hm

end ConsistentSubmodular.LowRollback

end

section

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q d₀ d p pa : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk1 : k ≤ 20 / 11) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpa : 0 ≤ pa) (_hd₀ : 0 ≤ d₀) (hd₀hi : d₀ ≤ 1 / 4)
    (hstrong : 1 / 2 ≤ pa ∨ d₀ ≤ pa * (1 - pa))
    (hparent : 0 ≤ (3 - k) * p - k * d - (4 - k) * (d₀ + pa))
    (hcredit : 0 ≤ 2 * k - 3 + 3 * (4 - k) * d₀ - k * p)
    (hchild : 0 ≤ cpoly q * d - npoly q - apoly q * p) :
    40 / 23 < k ∧ 20 - 11 * k + (2 * k - 5) * q < 0 := by
  obtain ⟨hc, ha, ha3, hA⟩ := child_coefficients q hq0 hq1
  have hk : 0 < k := by linarith
  have hC : 0 < cpoly q := by linarith
  have h4 : 0 < 4 - k := by linarith
  have hR : 0 ≤ SR k q := by
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 3 - k by linarith)
    have h2 := mul_le_mul_of_nonneg_left ha3 hk.le
    unfold SR
    nlinarith
  have hb : 0 < Sbeta k q := by
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 9 - 4 * k by linarith)
    have h2 := mul_le_mul_of_nonneg_left ha3 (show 0 ≤ 3 * k by positivity)
    unfold Sbeta
    nlinarith
  let v := min pa (1 / 2)
  have hv : 0 ≤ v := le_min hpa (by norm_num)
  have hvpa : v ≤ pa := min_le_left _ _
  have hdv : d₀ ≤ v * (1 - v) := by
    by_cases hh : 1 / 2 ≤ pa
    · have heq : v = 1 / 2 := min_eq_right hh
      rw [heq]
      nlinarith
    · have heq : v = pa := min_eq_left (le_of_not_ge hh)
      rw [heq]
      exact hstrong.resolve_left hh
  have hid : k * cpoly q * ((3 - k) * p - k * d - (4 - k) * (d₀ + pa))+
      k ^ 2 * (cpoly q * d - npoly q - apoly q * p)+
      SR k q * (2 * k - 3 + 3 * (4 - k) * d₀ - k * p) =
      -SS k q - (4 - k) * (k * cpoly q * pa - Sbeta k q * d₀) := by
    simp only [SR, SS, Sbeta]
    ring
  have h1 := mul_nonneg (mul_nonneg hk.le hC.le) hparent
  have h2 := mul_nonneg (sq_nonneg k) hchild
  have h3 := mul_nonneg hR hcredit
  have hsource : SS k q + (4 - k) * (k * cpoly q * pa - Sbeta k q * d₀) ≤ 0 := by
    linarith only [hid, h1, h2, h3]
  have hinner : Sbeta k q * v ^ 2 - SL k q * v ≤ k * cpoly q * pa - Sbeta k q * d₀ := by
    have h1 := mul_le_mul_of_nonneg_left hvpa (mul_nonneg hk.le hC.le)
    have h2 := mul_le_mul_of_nonneg_left hdv hb.le
    unfold SL
    nlinarith only [h1, h2]
  have hdom : SS k q + (4 - k) * (Sbeta k q * v ^ 2 - SL k q * v) ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hinner h4.le
    linarith
  have hnot : ¬ (0 ≤ 20 - 11 * k + (2 * k - 5) * q ∨ k ≤ 40 / 23) := by
    intro hregion
    have hS : 0 < SS k q := by
      rcases hregion with hH | hsmall
      · exact SS_positive_H k q hq0 hq1 hH
      · exact SS_positive_small k q hsmall hq0 hq1
    by_cases hL : SL k q ≤ 0
    · have h1 := mul_nonneg hb.le (sq_nonneg v)
      have h2 := mul_nonpos_of_nonpos_of_nonneg hL hv
      have h3 := mul_nonneg h4.le (show 0 ≤ Sbeta k q * v ^ 2 - SL k q * v by linarith)
      linarith
    · have hJ := SJ_positive k q hk0 hq0 hq1 (lt_of_not_ge hL)
      have hZ := mul_pos hk hJ
      have hid : 4 * Sbeta k q * (SS k q + (4 - k) * (Sbeta k q * v ^ 2 - SL k q * v)) =
          (4 - k) * (2 * Sbeta k q * v - SL k q) ^ 2 + k * SJ k q := by
        simp only [SS, SR, Sbeta, SL, SJ, SA, SB, SD, SE]
        ring
      have hleft := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * Sbeta k q by positivity) hdom
      have hright := mul_nonneg h4.le (sq_nonneg (2 * Sbeta k q * v - SL k q))
      linarith only [hid, hZ, hleft, hright]
  constructor
  · by_contra! h
    exact hnot (Or.inr h)
  · by_contra! h
    exact hnot (Or.inl h)

end
