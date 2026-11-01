-- Prove2me | solution 2 for CohenPriceFairness.LocalWelfare.lemma_1_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:16:10.925797+00:00
-- url     : https://prove2.me/submissions/9158809f-be79-4830-ae69-54f1860ad11c

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_market_profit_regular

open Filter Topology Asymptotics Set

namespace CohenPriceFairness.LocalWelfare.Sol_lemma_1_nondegenerate
open CohenPriceFairness.LocalWelfare

lemma l1_sign (w d r mm : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm0 : mm 0 ≠ 0)
    (hG : G < 0) :
    (0 < w 0 * (-d 0) * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * (-d 1) * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1))) ↔
    w 1 * d 1 * mm 1 * r 0 - w 0 * d 0 * mm 0 * r 1 < 0 := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hK : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
    have a : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) hr0
    have b : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr1.le
    linarith
  have hc : 0 < G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / (r 0 * r 1) :=
    div_pos (div_pos_of_neg_of_neg hG hK) (mul_pos_of_neg_of_neg hr0 hr1)
  have heq : w 0 * (-d 0) * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * (-d 1) * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
      G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / (r 0 * r 1) *
        -(w 1 * d 1 * mm 1 * r 0 - w 0 * d 0 * mm 0 * r 1) := by
    have := hr0.ne; have := hr1.ne; have := hK.ne
    field_simp
    ring
  rw [heq, mul_pos_iff_of_pos_left hc, neg_pos]


lemma l1_eta (x : ℝ) {P : ℝ → Prop} (h : ∀ᶠ y in 𝓝 x, P y) :
    ∃ η > 0, ∀ y ∈ Icc (x - η) (x + η), P y := by
  obtain ⟨ρ, hρ, H⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ρ / 2, half_pos hρ, fun y hy => H ?_⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]

theorem l1_claim (m : Market) (hm : m.Admissible) (b : Prices) (hb : BaselineOptimal m b)
    (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0)
    (k : Metric) (C : ℝ → Prop) (mm : Fin 2 → ℝ)
    (hMev : ∀ i, ∀ᶠ y in 𝓝 (b i), ContinuousAt (metricValue m k i) y)
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * (-demand m 0 (b 0)) *
        ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
          (mm 0 ^ 2 / deriv (deriv (profit m 0)) (b 0) +
            mm 1 ^ 2 / deriv (deriv (profit m 1)) (b 1))) * mm 0 /
          deriv (deriv (profit m 0)) (b 0)) +
      m.population 1 * (-demand m 1 (b 1)) *
        (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
          (mm 0 ^ 2 / deriv (deriv (profit m 0)) (b 0) +
            mm 1 ^ 2 / deriv (deriv (profit m 1)) (b 1))) * mm 1 /
          deriv (deriv (profit m 1)) (b 1))))) :
    SensitivityClaim m b k C := by
  obtain ⟨hb0, hloc, ⟨ηR, hηR, HR⟩, hRt, hS, -⟩ := market_profit_regular m hm b hb hr huniq
  obtain ⟨η0, hη0, H0⟩ := l1_eta (b 0) (hMev 0)
  obtain ⟨η1, hη1, H1⟩ := l1_eta (b 1) (hMev 1)
  have hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)) := by
    refine ⟨min ηR (min η0 η1), lt_min hηR (lt_min hη0 hη1), fun i => ?_⟩
    have hmR := min_le_left ηR (min η0 η1)
    have hm' := min_le_right ηR (min η0 η1)
    have hm0 := min_le_left η0 η1
    have hm1 := min_le_right η0 η1
    have hsR : Icc (b i - min ηR (min η0 η1)) (b i + min ηR (min η0 η1)) ⊆
        Icc (b i - ηR) (b i + ηR) := Icc_subset_Icc (by linarith) (by linarith)
    refine ⟨(HR i).mono hsR, ?_⟩
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · have hs : Icc (b 0 - min ηR (min η0 η1)) (b 0 + min ηR (min η0 η1)) ⊆
          Icc (b 0 - η0) (b 0 + η0) := Icc_subset_Icc (by linarith) (by linarith)
      exact fun y hy => (H0 y (hs hy)).continuousWithinAt
    · have hs : Icc (b 1 - min ηR (min η0 η1)) (b 1 + min ηR (min η0 η1)) ⊆
          Icc (b 1 - η1) (b 1 + η1) := Icc_subset_Icc (by linarith) (by linarith)
      exact fun y hy => (H1 y (hs hy)).continuousWithinAt
  exact sensitivityClaim_of_local_data m b k C (fun i => deriv (deriv (profit m i)) (b i)) mm
    (fun i => -demand m i (b i))
    hb0 (fun i => (hb i).2) hloc hcont hcurv hRt hMd hmm hS hgap hC

end CohenPriceFairness.LocalWelfare.Sol_lemma_1_nondegenerate

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_lemma_1_nondegenerate
open Filter Topology

theorem solution (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i)
    (hcurv : ∀ i, deriv (deriv (profit m i)) (b i) < 0) :
    (b 0 < b 1 → SensitivityClaim m b .price (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (demand m 0 (b 0) < demand m 1 (b 1) → (∀ i, deriv (demand m i) (b i) ≠ 0) →
      SensitivityClaim m b .demand (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (demand m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (demand m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) ∧
    (surplus m 0 (b 0) < surplus m 1 (b 1) → SensitivityClaim m b .surplus (fun D =>
      (0 < D ↔
        m.population 1 * (demand m 1 (b 1)) ^ 2 * deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * (demand m 0 (b 0)) ^ 2 * deriv (deriv (profit m 1)) (b 1) > 0))) ∧
    (nonbuyer m 0 (b 0) < nonbuyer m 1 (b 1) → (∀ i, deriv (nonbuyer m i) (b i) ≠ 0) →
      SensitivityClaim m b .nonbuyer (fun D =>
      (0 < D ↔
        m.population 1 * demand m 1 (b 1) * deriv (nonbuyer m 1) (b 1) *
          deriv (deriv (profit m 0)) (b 0) -
        m.population 0 * demand m 0 (b 0) * deriv (nonbuyer m 0) (b 0) *
          deriv (deriv (profit m 1)) (b 1) < 0))) := by
  obtain ⟨-, -, -, -, hS, hdpos⟩ := market_profit_regular m hm b hb hr huniq
  refine ⟨fun h01 => ?_, fun h01 hd => ?_, fun h01 => ?_, fun h01 hd => ?_⟩
  · refine l1_claim m hm b hb hr huniq hcurv .price _ (fun _ => 1)
      (fun i => Eventually.of_forall fun y => continuousAt_id) (fun i => hasDerivAt_id (b i))
      (Or.inl one_ne_zero) (ne_of_lt h01) ?_
    have h := l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun _ => 1)
      (metricValue m .price 0 (b 0) - metricValue m .price 1 (b 1)) hcurv one_ne_zero
      (by show b 0 - b 1 < 0; linarith)
    exact h.trans (by simp only [mul_one])
  · refine l1_claim m hm b hb hr huniq hcurv .demand _ (fun i => deriv (demand m i) (b i))
      (fun i => (hr i).1.1.mono fun y hy => hy.continuousAt)
      (fun i => (hr i).1.1.self_of_nhds.hasDerivAt)
      (Or.inl (hd 0)) (ne_of_lt h01) ?_
    exact l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => deriv (demand m i) (b i))
      (metricValue m .demand 0 (b 0) - metricValue m .demand 1 (b 1)) hcurv (hd 0)
      (by show demand m 0 (b 0) - demand m 1 (b 1) < 0; linarith)
  · refine l1_claim m hm b hb hr huniq hcurv .surplus _ (fun i => -demand m i (b i))
      (fun i => (hr i).2.1.1.mono fun y hy => hy.continuousAt) hS
      (Or.inl (neg_ne_zero.mpr (hdpos 0).ne')) (ne_of_lt h01) ?_
    have h := l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => -demand m i (b i))
      (metricValue m .surplus 0 (b 0) - metricValue m .surplus 1 (b 1)) hcurv
      (neg_ne_zero.mpr (hdpos 0).ne')
      (by show surplus m 0 (b 0) - surplus m 1 (b 1) < 0; linarith)
    refine h.trans ?_
    simp only [gt_iff_lt]
    constructor <;> intro h' <;> nlinarith [h']
  · refine l1_claim m hm b hb hr huniq hcurv .nonbuyer _ (fun i => deriv (nonbuyer m i) (b i))
      (fun i => (hr i).2.2.1.1.mono fun y hy => hy.continuousAt)
      (fun i => (hr i).2.2.1.1.self_of_nhds.hasDerivAt)
      (Or.inl (hd 0)) (ne_of_lt h01) ?_
    exact l1_sign m.population (fun i => demand m i (b i))
      (fun i => deriv (deriv (profit m i)) (b i)) (fun i => deriv (nonbuyer m i) (b i))
      (metricValue m .nonbuyer 0 (b 0) - metricValue m .nonbuyer 1 (b 1)) hcurv (hd 0)
      (by show nonbuyer m 0 (b 0) - nonbuyer m 1 (b 1) < 0; linarith)

