-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.exp_price_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:58.15826+00:00
-- url     : https://prove2.me/submissions/b58be2fd-34d5-496a-95b6-f46c26965528

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_profit_regular

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

namespace CohenPriceFairness.LocalWelfare.Sol_exp_price_claim

/-- `sensitivityClaim_of_local_data`, with the metric's continuity given on `Ioi 0`. -/
theorem eb_claim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hRc : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)))
    (hMc : ∀ i, ContinuousOn (metricValue m k i) (Ioi 0))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  obtain ⟨η, hη, hRc⟩ := hRc
  refine sensitivityClaim_of_local_data m b k C r mm σ hb hopt hloc ?_ hr hRt hMd hmm hSd hgap hC
  have hm : 0 < min (b 0) (b 1) := lt_min (hb 0) (hb 1)
  refine ⟨min η (min (b 0) (b 1) / 2), lt_min hη (by positivity), fun i => ⟨(hRc i).mono ?_, (hMc i).mono ?_⟩⟩
  · have := min_le_left η (min (b 0) (b 1) / 2)
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  · intro p hp
    have hmin : min (b 0) (b 1) ≤ b i := by
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
    have := min_le_right η (min (b 0) (b 1) / 2)
    simp only [mem_Ioi]; linarith [hp.1]

lemma eb_K_neg (mm r : Fin 2 → ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) :
    mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
  have a0 : mm 0 ^ 2 / r 0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 0).le
  have a1 : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 1).le
  rcases hmm with h | h
  · have : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 0)
    linarith
  · have : mm 1 ^ 2 / r 1 < 0 := div_neg_of_pos_of_neg (by positivity) (hr 1)
    linarith

lemma eb_D_eq (w σ mm r : Fin 2 → ℝ) (G : ℝ) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
    (G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) *
      (-(mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)⁻¹) := by
  ring

lemma eb_D_pos (w σ mm r : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (h : 0 < G * (w 0 * σ 0 * mm 0 / r 0 - w 1 * σ 1 * mm 1 / r 1)) :
    0 < w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) := by
  rw [eb_D_eq]
  have := eb_K_neg mm r hr hmm
  exact mul_pos h (neg_pos.mpr (inv_lt_zero.mpr this))


lemma eb_X (d l q mm : Fin 2 → ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i) (hq : ∀ i, 0 < q i) :
    d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)) =
      mm 0 / l 0 - mm 1 / l 1 := by
  have := hd 0; have := hd 1; have := hl 0; have := hl 1; have := hq 0; have := hq 1
  field_simp


lemma eb_Dexp_pos (d l q mm : Fin 2 → ℝ) (G : ℝ) (hd : ∀ i, 0 < d i) (hl : ∀ i, 0 < l i)
    (hq : ∀ i, 0 < q i) (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0) (h : 0 < G * (mm 0 / l 0 - mm 1 / l 1)) :
    0 < d 0 * (-q 0) * ((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 0 / (-(d 0 * l 0 * q 0))) +
      d 1 * (-q 1) * (-((-G / (mm 0 ^ 2 / (-(d 0 * l 0 * q 0)) + mm 1 ^ 2 / (-(d 1 * l 1 * q 1))))
        * mm 1 / (-(d 1 * l 1 * q 1)))) := by
  have hr : ∀ i, (fun i => -(d i * l i * q i)) i < 0 := fun i => by
    have := hd i; have := hl i; have := hq i
    simp only [neg_lt_zero]; positivity
  have := eb_D_pos d (fun i => -q i) mm (fun i => -(d i * l i * q i)) G hr hmm (by
    show 0 < G * (d 0 * (-q 0) * mm 0 / (-(d 0 * l 0 * q 0)) - d 1 * (-q 1) * mm 1 / (-(d 1 * l 1 * q 1)))
    rw [eb_X d l q mm hd hl hq]; exact h)
  exact this


end CohenPriceFairness.LocalWelfare.Sol_exp_price_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_exp_price_claim
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics Real Set

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i) (hne : rate 0 ≠ rate 1)
    (hlaw : ∀ i, m.law i = expMeasure (rate i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .price (fun D => 0 < D) := by
  obtain ⟨hBO, hreg⟩ := exp_profit_regular m hd hc rate hrate hlaw
  obtain ⟨hbpos, hloc, hRc, hRt0, hSd0, hdem0⟩ := hreg b hb
  have hbi := (hBO b).1 hb
  have hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i) := fun i => (hb i).2
  obtain ⟨q, hq⟩ : ∃ q : Fin 2 → ℝ, ∀ i, q i = exp (-(1 + rate i * m.cost)) := ⟨_, fun _ => rfl⟩
  have hqpos : ∀ i, 0 < q i := fun i => by rw [hq i]; exact exp_pos _
  have hdem : ∀ i, demand m i (b i) = q i := fun i => by rw [hq i]; exact hdem0 i
  have hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) -
      (fun i => -(m.population i * rate i * q i)) i / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) :=
    fun i => by simp only [hq i]; exact hRt0 i
  have hr : ∀ i, (fun i => -(m.population i * rate i * q i)) i < 0 := fun i => by
    have := hd i; have := hrate i; have := hqpos i
    simp only [neg_lt_zero]; positivity
  have hSd : ∀ i, HasDerivAt (surplus m i) ((fun i => -q i) i) (b i) := fun i => by
    have := hSd0 i; rw [hdem i] at this; exact this
  have hG : b 0 - b 1 ≠ 0 := by
    rw [hbi 0, hbi 1]; intro h; apply hne
    have : 1 / rate 0 = 1 / rate 1 := by linarith
    simpa using this
  refine eb_claim m b .price _ _ (fun _ => 1) _ hbpos hopt hloc hRc
    (fun i => continuous_id.continuousOn) hr hRt (fun i => hasDerivAt_id' (b i))
    (Or.inl one_ne_zero) hSd (sub_ne_zero.mp hG) ?_
  refine eb_Dexp_pos m.population rate q (fun _ => 1)
    (metricValue m .price 0 (b 0) - metricValue m .price 1 (b 1)) hd hrate hqpos
    (Or.inl one_ne_zero) ?_
  show 0 < (b 0 - b 1) * (1 / rate 0 - 1 / rate 1)
  have : b 0 - b 1 = 1 / rate 0 - 1 / rate 1 := by rw [hbi 0, hbi 1]; ring
  rw [this] at hG ⊢; exact mul_self_pos.mpr hG
