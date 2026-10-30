-- Prove2me | solution 1 for DisclosureDiscretion.InfoSystem.proposition_9
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:51:40.407997+00:00
-- url     : https://prove2.me/submissions/a38df82d-d07e-454e-920e-11fc16d1874a

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

open MeasureTheory Set DisclosureDiscretion.InfoSystem

/-- On `[a, b]`, a function agreeing on `Ioc a b` with a continuous `g` is interval
integrable and has the same interval integral as `g`. -/
private lemma ii_of_eqOn {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g)
    (h : EqOn f g (Ioc a b)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = ∫ x in a..b, g x := by
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun h.symm measurableSet_Ioc
  · rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun measurableSet_Ioc h

theorem solution : ¬ (∀ (cbar t p k : ℝ), Standing cbar t p k →
    (t * cbar / 2 ≤ k →
      expPriceP cbar t p k < expPriceN cbar t k ∧
      ∀ x q : ℝ, IsDEquilibrium cbar t p k x q →
        expPriceD cbar t p k x q < expPriceN cbar t k) ∧
    (k2A cbar t p ≤ k → k < t * cbar / 2 →
      (∃ x q : ℝ, IsDEquilibrium cbar t p k x q ∧
        expPriceN cbar t k < expPriceD cbar t p k x q ∧
        expPriceP cbar t p k < expPriceD cbar t p k x q) ∧
      (k2A cbar t p < k → ∀ x q : ℝ, IsDEquilibrium cbar t p k x q →
        expPriceN cbar t k < expPriceD cbar t p k x q ∧
        expPriceP cbar t p k < expPriceD cbar t p k x q)) ∧
    (k < k2A cbar t p →
      expPriceN cbar t k < expPriceP cbar t p k ∧
      (∃ x q : ℝ, IsDEquilibrium cbar t p k x q ∧
        expPriceD cbar t p k x q < expPriceP cbar t p k) ∧
      (∀ x q : ℝ, IsDEquilibrium cbar t p k x q → k / t < x →
        expPriceD cbar t p k x q < expPriceP cbar t p k))) := by
  intro H
  -- parameters
  set p : ℝ := 1250000 / 1250123 with hp
  have hS : Standing 1 (19 / 20) p (19 / 640) := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num [hp], by norm_num [hp],
      by norm_num⟩
  have hkt : (19 / 640 : ℝ) / (19 / 20) = 1 / 32 := by norm_num
  have hsp : silencePrice (19 / 20) (1 / 32) (472 / 475) = 7 / 4000 := by
    unfold silencePrice; norm_num
  -- k > k2A
  have hk2A : k2A 1 (19 / 20) p < 19 / 640 := by
    have hy : (0 : ℝ) < (1 - p) + 19 / 640 * p * (1 - (19 / 20) ^ 2) / (19 / 20) := by
      norm_num [hp]
    have hsq : Real.sqrt ((1 - p) * (1 - p * (19 / 20) ^ 2)) <
        (1 - p) + 19 / 640 * p * (1 - (19 / 20) ^ 2) / (19 / 20) := by
      rw [Real.sqrt_lt' hy]; norm_num [hp]
    unfold k2A
    have hden : (0 : ℝ) < p * (1 - (19 / 20) ^ 2) := by norm_num [hp]
    rw [div_lt_iff₀ hden]
    have : (19 / 20 : ℝ) * 1 * (Real.sqrt ((1 - p) * (1 - p * (19 / 20) ^ 2)) - (1 - p)) <
        19 / 20 * 1 * (((1 - p) + 19 / 640 * p * (1 - (19 / 20) ^ 2) / (19 / 20)) - (1 - p)) := by
      nlinarith
    calc _ < _ := this
      _ = 19 / 640 * (p * (1 - (19 / 20) ^ 2)) := by ring
  -- the nondisclosure set
  have hnd : ndSet 1 (19 / 20) (19 / 640) (7 / 4000) =
      Ico 0 (7 / 4000) ∪ Ioo (1 / 32) (7 / 200) := by
    ext c
    simp only [ndSet, discPrice, mem_Icc, mem_union, mem_Ico, mem_Ioo, hkt]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      split_ifs at h with hc
      · left; exact ⟨h0, h⟩
      · right; push Not at hc; exact ⟨hc, by linarith⟩
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · refine ⟨⟨h0, by linarith⟩, ?_⟩
        rw [if_pos (by linarith)]; exact h1
      · refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [if_neg (by linarith)]; linarith
  have hdisj : Disjoint (Ico (0 : ℝ) (7 / 4000)) (Ioo (1 / 32) (7 / 200)) := by
    rw [Set.disjoint_left]
    rintro c ⟨_, h1⟩ ⟨h2, _⟩
    linarith
  have hvol : (volume (Ico (0 : ℝ) (7 / 4000) ∪ Ioo (1 / 32) (7 / 200))).toReal =
      7 / 4000 + (7 / 200 - 1 / 32) := by
    rw [measure_union hdisj measurableSet_Ioo, Real.volume_Ico, Real.volume_Ioo,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hint : (∫ c in Ico (0 : ℝ) (7 / 4000) ∪ Ioo (1 / 32) (7 / 200), c) =
      ((7 / 4000) ^ 2 - 0 ^ 2) / 2 + ((7 / 200) ^ 2 - (1 / 32) ^ 2) / 2 := by
    rw [setIntegral_union (f := fun c : ℝ => c) hdisj measurableSet_Ioo
      (continuous_id.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      (continuous_id.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      ← intervalIntegral.integral_of_le (by norm_num), integral_id, integral_id]
  have hsv : silenceValue 1 p (ndSet 1 (19 / 20) (19 / 640) (7 / 4000)) = 1 / 32 := by
    unfold silenceValue
    rw [hnd, hvol, hint]
    rw [div_eq_iff (by norm_num [hp])]
    norm_num [hp]
  have hEq : IsDEquilibrium 1 (19 / 20) p (19 / 640) (1 / 32) (472 / 475) := by
    refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro h; rw [hkt] at h; exact absurd h (lt_irrefl _)
    · intro h; rw [hkt] at h; exact absurd h (lt_irrefl _)
    · rw [hsp, hsv]
  -- expected prices
  have hEN : expPriceN 1 (19 / 20) (19 / 640) = (1 - 19 / 20) * (1 / 2) := by
    unfold expPriceN; rw [if_pos (by norm_num)]
  have hIV : (∫ c in Icc (0 : ℝ) 1, discPrice (19 / 20) (19 / 640) c) =
      ((1 / 32) ^ 2 - 0 ^ 2) / 2 + (1 - 19 / 20) * ((1 ^ 2 - (1 / 32) ^ 2) / 2) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have e1 := ii_of_eqOn (f := discPrice (19 / 20) (19 / 640)) (g := fun c => c)
      (a := 0) (b := 1 / 32) (by norm_num) continuous_id (by
        intro c hc; simp only [discPrice, hkt]; rw [if_pos hc.2])
    have e2 := ii_of_eqOn (f := discPrice (19 / 20) (19 / 640))
      (g := fun c => (1 - 19 / 20) * c)
      (a := 1 / 32) (b := 1) (by norm_num) (continuous_const.mul continuous_id) (by
        intro c hc; simp only [discPrice, hkt]; rw [if_neg (not_le.mpr hc.1)])
    rw [← intervalIntegral.integral_add_adjacent_intervals e1.1 e2.1, e1.2, e2.2,
      intervalIntegral.integral_const_mul, integral_id, integral_id]
  have hEP : expPriceP 1 (19 / 20) p (19 / 640) =
      (1 - p) * ((1 - 19 / 20) * (1 / 2)) +
        p * (((1 / 32) ^ 2 - 0 ^ 2) / 2 + (1 - 19 / 20) * ((1 ^ 2 - (1 / 32) ^ 2) / 2)) / 1 := by
    unfold expPriceP; rw [hEN, hIV]
  have hIM : (∫ c in Icc (0 : ℝ) 1, max (discPrice (19 / 20) (19 / 640) c) (7 / 4000)) =
      7 / 4000 * (7 / 4000 - 0) + ((1 / 32) ^ 2 - (7 / 4000) ^ 2) / 2 +
        7 / 4000 * (7 / 200 - 1 / 32) + (1 - 19 / 20) * ((1 ^ 2 - (7 / 200) ^ 2) / 2) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have e1 := ii_of_eqOn (f := fun c => max (discPrice (19 / 20) (19 / 640) c) (7 / 4000))
      (g := fun _ => (7 / 4000 : ℝ))
      (a := 0) (b := 7 / 4000) (by norm_num) continuous_const (by
        intro c hc; simp only [discPrice, hkt]
        rw [if_pos (by linarith [hc.2])]; exact max_eq_right hc.2)
    have e2 := ii_of_eqOn (f := fun c => max (discPrice (19 / 20) (19 / 640) c) (7 / 4000))
      (g := fun c => c)
      (a := 7 / 4000) (b := 1 / 32) (by norm_num) continuous_id (by
        intro c hc; simp only [discPrice, hkt]
        rw [if_pos hc.2]; exact max_eq_left hc.1.le)
    have e3 := ii_of_eqOn (f := fun c => max (discPrice (19 / 20) (19 / 640) c) (7 / 4000))
      (g := fun _ => (7 / 4000 : ℝ))
      (a := 1 / 32) (b := 7 / 200) (by norm_num) continuous_const (by
        intro c hc; simp only [discPrice, hkt]
        rw [if_neg (not_le.mpr hc.1)]; exact max_eq_right (by linarith [hc.2]))
    have e4 := ii_of_eqOn (f := fun c => max (discPrice (19 / 20) (19 / 640) c) (7 / 4000))
      (g := fun c => (1 - 19 / 20) * c)
      (a := 7 / 200) (b := 1) (by norm_num) (continuous_const.mul continuous_id) (by
        intro c hc; simp only [discPrice, hkt]
        rw [if_neg (by linarith [hc.1])]; exact max_eq_left (by linarith [hc.1]))
    rw [← intervalIntegral.integral_add_adjacent_intervals (e1.1.trans e2.1) (e3.1.trans e4.1),
      ← intervalIntegral.integral_add_adjacent_intervals e1.1 e2.1,
      ← intervalIntegral.integral_add_adjacent_intervals e3.1 e4.1,
      e1.2, e2.2, e3.2, e4.2, intervalIntegral.integral_const_mul, integral_id, integral_id,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hED : expPriceD 1 (19 / 20) p (19 / 640) (1 / 32) (472 / 475) =
      (1 - p) * (7 / 4000) + p * (7 / 4000 * (7 / 4000 - 0) + ((1 / 32) ^ 2 - (7 / 4000) ^ 2) / 2 +
        7 / 4000 * (7 / 200 - 1 / 32) + (1 - 19 / 20) * ((1 ^ 2 - (7 / 200) ^ 2) / 2)) / 1 := by
    unfold expPriceD; rw [hsp, hIM]
  have hpart := ((H 1 (19 / 20) p (19 / 640) hS).2.1 hk2A.le (by norm_num)).2 hk2A
    (1 / 32) (472 / 475) hEq
  have hbad := hpart.2
  rw [hEP, hED] at hbad
  norm_num [hp] at hbad
