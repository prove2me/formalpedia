-- Prove2me | solution 1 for CustomerVoice.Payoffs.quality_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:41:51.032175+00:00
-- url     : https://prove2.me/submissions/1a06c4aa-74bb-4728-8162-681ec927d7b2

import Mathlib
import Definitions.Def_CustomerVoice_Payoffs_Setting

set_option autoImplicit false
open CustomerVoice.Payoffs
abbrev BType := CustomerVoice.ALearn.BType

lemma cv_sum2 (f : BType → ℝ) : ∑ t : BType, f t = f .H + f .L := by
  show ∑ t ∈ ({CustomerVoice.ALearn.BType.H, CustomerVoice.ALearn.BType.L} : Finset BType), f t = _
  rw [Finset.sum_pair (by decide)]

lemma cv_pos (M : Model) (hM : M.Standing) :
    0 < M.thL ∧ M.thL < M.thH ∧ 0 < M.alpha ∧ M.alpha < 1 ∧ 0 < M.gamma ∧ M.gamma < 1 ∧
      0 < M.k ∧ 0 < M.s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

lemma cv_theta_pos (M : Model) (hM : M.Standing) (t : BType) : 0 < M.theta t := by
  obtain ⟨h1, h2, -⟩ := cv_pos M hM
  cases t
  · show 0 < M.thH; linarith
  · show 0 < M.thL; linarith

lemma cv_theta_le (M : Model) (hM : M.Standing) (t : BType) : M.theta t ≤ M.thH := by
  obtain ⟨h1, h2, -⟩ := cv_pos M hM
  cases t
  · exact le_refl _
  · show M.thL ≤ M.thH; linarith

lemma cv_alphaW_pos (M : Model) (hM : M.Standing) (t : BType) : 0 < M.alphaW t := by
  obtain ⟨-, -, h3, h4, -⟩ := cv_pos M hM
  cases t
  · show 0 < M.alpha; linarith
  · show 0 < 1 - M.alpha; linarith

lemma cv_qA_pos (M : Model) (hM : M.Standing) (t : BType) : 0 < M.qA t := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have := cv_theta_pos M hM t
  unfold Model.qA
  positivity

lemma cv_qA_lt_qO (M : Model) (hM : M.Standing) (t : BType) : M.qA t < M.qO t := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  unfold Model.qA Model.qO
  apply lt_min
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hg ht) (add_pos hs (mul_pos hg hk))]
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos ht hs]

lemma cv_k_qO_le (M : Model) (hM : M.Standing) (t : BType) :
    M.k * M.qO t ≤ M.theta t / 2 := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have h : M.qO t ≤ M.theta t / (2 * M.k) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h
  linarith

lemma cv_v_diff (M : Model) (hM : M.Standing) (t : BType) (q : ℝ) :
    M.v (M.qA t) (M.theta t) - M.v q (M.theta t) =
      (M.s + M.gamma * M.k) * (q - M.qA t) ^ 2 := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have hc : 2 * M.s + 2 * M.gamma * M.k ≠ 0 := by positivity
  unfold Model.v Model.qA
  field_simp
  ring

lemma cv_UA (M : Model) (hM : M.Standing) (t : BType) :
    M.UA t = (1 - M.gamma) * (M.qA t * (M.theta t - M.k * M.qA t)) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  have h1 := cv_qA_pos M hM t
  have h2 := cv_qA_lt_qO M hM t
  have h3 := cv_k_qO_le M hM t
  have hp : 0 ≤ M.theta t * M.qA t - M.k * M.qA t ^ 2 := by
    have : M.k * M.qA t ≤ M.k * M.qO t := mul_le_mul_of_nonneg_left h2.le hk.le
    nlinarith
  unfold Model.UA Model.uA
  rw [sub_self, max_self, max_eq_left hp]
  ring

lemma cv_UO (M : Model) (hM : M.Standing) (t : BType) :
    M.UO t = (1 - M.gamma) * (M.qO t * (M.theta t - M.k * M.qO t)) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  have h1 := cv_qA_pos M hM t
  have h2 := cv_qA_lt_qO M hM t
  have h3 := cv_k_qO_le M hM t
  have hp : 0 ≤ M.theta t * M.qO t - M.k * M.qO t ^ 2 := by
    nlinarith
  unfold Model.UO Model.mu
  rw [sub_self, max_self, max_eq_left hp]
  ring

lemma cv_UO_sub_UA (M : Model) (hM : M.Standing) (t : BType) :
    M.UO t - M.UA t = (1 - M.gamma) * ((M.qO t - M.qA t) *
      (M.theta t - M.k * (M.qO t + M.qA t))) := by
  rw [cv_UO M hM t, cv_UA M hM t]; ring

lemma cv_standing_withS (M : Model) (hM : M.Standing) (s' : ℝ) (hs : 0 < s') :
    (M.withS s').Standing := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := cv_pos M hM
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hs⟩

lemma cv_qO_eq (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) (t : BType) :
    M.qO t = M.theta t / (2 * M.k) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  unfold Model.qO
  apply min_eq_right
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hle ht.le]

lemma cv_gap (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) (t : BType) :
    M.qO t - M.qA t = M.theta t * M.s / (2 * M.k * (M.s + M.gamma * M.k)) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have hc : M.s + M.gamma * M.k ≠ 0 := by positivity
  rw [cv_qO_eq M hM hle]
  unfold Model.qA
  field_simp
  ring

lemma cv_gap_le (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) (t : BType) :
    M.qO t - M.qA t ≤ M.theta t * M.s / (2 * M.gamma * M.k ^ 2) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  rw [cv_gap M hM hle]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ M.theta t * M.s := by positivity
  nlinarith [mul_nonneg this (mul_nonneg (mul_nonneg hk.le hk.le) hs.le)]

lemma cv_gap_nonneg (M : Model) (hM : M.Standing) (t : BType) : 0 ≤ M.qO t - M.qA t := by
  linarith [cv_qA_lt_qO M hM t]

lemma cv_d_le (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) (t : BType) :
    M.v (M.qA t) (M.theta t) - M.v (M.qO t) (M.theta t) ≤
      M.theta t ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) := by
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  rw [cv_v_diff M hM t]
  have g0 := cv_gap_nonneg M hM t
  have g1 := cv_gap_le M hM hle t
  have g2 : (M.qO t - M.qA t) ^ 2 ≤ (M.theta t * M.s / (2 * M.gamma * M.k ^ 2)) ^ 2 :=
    pow_le_pow_left₀ g0 g1 2
  have hcb : M.s + M.gamma * M.k ≤ 2 * (M.gamma * M.k) := by linarith
  have : (M.s + M.gamma * M.k) * (M.qO t - M.qA t) ^ 2 ≤
      2 * (M.gamma * M.k) * (M.theta t * M.s / (2 * M.gamma * M.k ^ 2)) ^ 2 :=
    mul_le_mul hcb g2 (sq_nonneg _) (by positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

lemma cv_U_le (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) (t : BType) :
    M.UO t - M.UA t ≤
      (1 - M.gamma) * M.theta t ^ 2 / (2 * M.gamma * M.k ^ 2) * M.s := by
  obtain ⟨-, -, -, -, hg, hg1, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  rw [cv_UO_sub_UA M hM t]
  have g0 := cv_gap_nonneg M hM t
  have g1 := cv_gap_le M hM hle t
  have h1 := cv_qA_pos M hM t
  have h2 := cv_qA_lt_qO M hM t
  have h3 : 0 ≤ M.qO t - M.qA t := g0
  have hq : 0 < M.qO t := lt_trans h1 h2
  have h4 : (M.qO t - M.qA t) * (M.theta t - M.k * (M.qO t + M.qA t)) ≤
      (M.qO t - M.qA t) * M.theta t := by
    apply mul_le_mul_of_nonneg_left _ g0
    nlinarith [mul_pos hk hq, mul_pos hk h1]
  have h5 : (M.qO t - M.qA t) * M.theta t ≤
      M.theta t * M.s / (2 * M.gamma * M.k ^ 2) * M.theta t :=
    mul_le_mul_of_nonneg_right g1 ht.le
  have h6 : 0 ≤ 1 - M.gamma := by linarith
  calc (1 - M.gamma) * ((M.qO t - M.qA t) * (M.theta t - M.k * (M.qO t + M.qA t)))
      ≤ (1 - M.gamma) * (M.theta t * M.s / (2 * M.gamma * M.k ^ 2) * M.theta t) :=
        mul_le_mul_of_nonneg_left (h4.trans h5) h6
    _ = _ := by field_simp

lemma cv_VA_VO_le (M : Model) (hM : M.Standing) (hle : M.s ≤ M.gamma * M.k) :
    M.VA - M.VO ≤ M.thH ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) := by
  obtain ⟨h1, h2, h3, h4, hg, -, hk, hs⟩ := cv_pos M hM
  have hH := cv_d_le M hM hle CustomerVoice.ALearn.BType.H
  have hL := cv_d_le M hM hle CustomerVoice.ALearn.BType.L
  have hL' : M.thL ^ 2 ≤ M.thH ^ 2 := pow_le_pow_left₀ h1.le h2.le 2
  have hL2 : M.thL ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) ≤
      M.thH ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hL' (sq_nonneg _)
  have hH' : M.v (M.qA CustomerVoice.ALearn.BType.H) M.thH -
      M.v (M.qO CustomerVoice.ALearn.BType.H) M.thH ≤
      M.thH ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) := hH
  have hL'' : M.v (M.qA CustomerVoice.ALearn.BType.L) M.thL -
      M.v (M.qO CustomerVoice.ALearn.BType.L) M.thL ≤
      M.thH ^ 2 * M.s ^ 2 / (2 * M.gamma * M.k ^ 3) := le_trans hL hL2
  have e : M.VA - M.VO = M.alpha * (M.v (M.qA CustomerVoice.ALearn.BType.H) M.thH -
      M.v (M.qO CustomerVoice.ALearn.BType.H) M.thH) +
      (1 - M.alpha) * (M.v (M.qA CustomerVoice.ALearn.BType.L) M.thL -
      M.v (M.qO CustomerVoice.ALearn.BType.L) M.thL) := by
    unfold Model.VA Model.VO
    rw [cv_sum2, cv_sum2]
    simp only [Model.alphaW, Model.theta]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hH' h3.le,
    mul_le_mul_of_nonneg_left hL'' (by linarith : (0 : ℝ) ≤ 1 - M.alpha)]

theorem solution (M : Model) (hM : M.Standing) :
    ∀ t : CustomerVoice.ALearn.BType,
      Filter.Tendsto (fun s' : ℝ => (M.withS s').qO t - (M.withS s').qA t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro t
  obtain ⟨-, -, -, -, hg, -, hk, hs⟩ := cv_pos M hM
  have ht := cv_theta_pos M hM t
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (M.gamma * M.k) (ε * (2 * M.gamma * M.k ^ 2) / M.theta t), by positivity, ?_⟩
  intro s' hs' hd
  beta_reduce
  have hs'0 : 0 < s' := hs'
  rw [Real.dist_eq, sub_zero, abs_of_pos hs'0] at hd
  have hlt1 : s' < M.gamma * M.k := lt_of_lt_of_le hd (min_le_left _ _)
  have hlt2 : s' < ε * (2 * M.gamma * M.k ^ 2) / M.theta t :=
    lt_of_lt_of_le hd (min_le_right _ _)
  have hS := cv_standing_withS M hM s' hs'0
  have hle : (M.withS s').s ≤ (M.withS s').gamma * (M.withS s').k := hlt1.le
  have g0 := cv_gap_nonneg _ hS t
  have g1 := cv_gap_le _ hS hle t
  rw [Real.dist_eq, sub_zero, abs_of_nonneg g0]
  refine lt_of_le_of_lt g1 ?_
  show M.theta t * s' / (2 * M.gamma * M.k ^ 2) < ε
  rw [div_lt_iff₀ (by positivity)]
  rw [lt_div_iff₀ ht] at hlt2
  nlinarith
