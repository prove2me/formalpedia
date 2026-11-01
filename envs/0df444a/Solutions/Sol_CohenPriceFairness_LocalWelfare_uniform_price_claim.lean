-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_price_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:51.786721+00:00
-- url     : https://prove2.me/submissions/1824eaea-bb6c-4e0f-a9d5-b0a7623b50fd

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_price_claim

open CohenPriceFairness.LocalWelfare

theorem ub_formula_eq (w σ r mm K : Fin 2 → ℝ) (G : ℝ) (hr : ∀ i, r i < 0)
    (hS : mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 ≠ 0)
    (hw : ∀ i, w i * σ i = K i * r i / 2) :
    w 0 * σ 0 * ((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      w 1 * σ 1 * (-((-G / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)) =
    -(G * (K 0 * mm 0 - K 1 * mm 1)) / (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1) / 2 := by
  rw [hw 0, hw 1]
  have h0 := (hr 0).ne
  have h1 := (hr 1).ne
  generalize mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 = S at hS ⊢
  field_simp
  ring

theorem ub_sigma_neg (r mm : Fin 2 → ℝ) (hr : ∀ i, r i < 0) (h0 : mm 0 ≠ 0) :
    mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1 < 0 := by
  have a : mm 0 ^ 2 / r 0 < 0 := div_neg_of_pos_of_neg (sq_pos_of_ne_zero h0) (hr 0)
  have b : mm 1 ^ 2 / r 1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hr 1).le
  linarith

/-- Profit-side data from `uniform_profit_regular`, metric-side data as hypotheses. -/
theorem ub_main (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hcb : m.cost < min (bb 0) (bb 1))
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (b : Prices) (hb : BaselineOptimal m b)
    (k : Metric) (C : ℝ → Prop) (mm : Fin 2 → ℝ)
    (hcM : ∃ η > 0, ∀ i, ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i)) (hmm0 : mm 0 ≠ 0)
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : ∀ S : ℝ, S < 0 → C (-((metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) *
        ((bb 0 - b 0) * mm 0 - (bb 1 - b 1) * mm 1)) / S / 2)) :
    SensitivityClaim m b k C := by
  obtain ⟨hiff, hreg⟩ := uniform_profit_regular m hd hc bb hbb hcb hlaw
  obtain ⟨hpos, hloc, ⟨η1, hη1, hcR⟩, hRt, hSd, hdem⟩ := hreg b hb
  have hbi := (hiff b).1 hb
  obtain ⟨η2, hη2, hcM⟩ := hcM
  have hr : ∀ i, -2 * m.population i / bb i < 0 :=
    fun i => div_neg_of_neg_of_pos (by linarith [hd i]) (hbb i)
  have hsub : ∀ η' : ℝ, ∀ i, min η1 η2 ≤ η' →
      Set.Icc (b i - min η1 η2) (b i + min η1 η2) ⊆ Set.Icc (b i - η') (b i + η') :=
    fun η' i h => Set.Icc_subset_Icc (by linarith) (by linarith)
  refine sensitivityClaim_of_local_data m b k C (fun i => -2 * m.population i / bb i) mm
    (fun i => -demand m i (b i)) hpos (fun i => (hb i).2) hloc
    ⟨min η1 η2, lt_min hη1 hη2, fun i => ⟨(hcR i).mono (hsub η1 i (min_le_left _ _)),
      (hcM i).mono (hsub η2 i (min_le_right _ _))⟩⟩ hr hRt hMd (Or.inl hmm0) hSd hgap ?_
  rw [ub_formula_eq m.population (fun i => -demand m i (b i))
    (fun i => -2 * m.population i / bb i) mm (fun i => bb i - b i) _ hr
    (ub_sigma_neg _ mm hr hmm0).ne ?_]
  · exact hC _ (ub_sigma_neg _ mm hr hmm0)
  · intro i; rw [hdem i, hbi i]; have := (hbb i).ne'; field_simp; ring

end CohenPriceFairness.LocalWelfare.Sol_uniform_price_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_price_claim

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .price (fun D => 0 < D) := by
  have hbi := ((uniform_profit_regular m hd hc bb hbb hcb hlaw).1 b).1 hb
  have hp0 := hbi 0
  have hp1 := hbi 1
  have hne' : bb 0 - bb 1 ≠ 0 := sub_ne_zero.mpr hne
  refine ub_main m hd hc bb hbb hcb hlaw b hb .price _ (fun _ => 1)
    ⟨1, one_pos, fun i => continuous_id.continuousOn⟩
    (fun i => hasDerivAt_id (b i)) one_ne_zero ?_ (fun S hS => ?_)
  · show b 0 ≠ b 1
    rw [hp0, hp1]; intro h; apply hne; linarith
  · show 0 < -((b 0 - b 1) * ((bb 0 - b 0) * 1 - (bb 1 - b 1) * 1)) / S / 2
    rw [hp0, hp1]
    have e : ((bb 0 + m.cost) / 2 - (bb 1 + m.cost) / 2) *
        ((bb 0 - (bb 0 + m.cost) / 2) * 1 - (bb 1 - (bb 1 + m.cost) / 2) * 1) =
        (bb 0 - bb 1) ^ 2 / 4 := by ring
    rw [e]
    have := sq_pos_of_ne_zero hne'
    exact half_pos (div_pos_of_neg_of_neg (by linarith) hS)
