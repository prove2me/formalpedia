-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_surplus_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:54.929215+00:00
-- url     : https://prove2.me/submissions/09edad3d-e193-45f6-92f2-1869055ef895

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_surplus

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_surplus_claim

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

/-- A neighbourhood of the baseline price inside `(0, bb i)`. -/
theorem ub_nbhd (m : Market) (hc : 0 ≤ m.cost) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hcb : m.cost < min (bb 0) (bb 1)) (b : Prices) (hbi : ∀ i, b i = (bb i + m.cost) / 2) :
    (∀ i, b i ∈ Set.Ioo 0 (bb i)) ∧
    ∃ η > 0, ∀ i, Set.Icc (b i - η) (b i + η) ⊆ Set.Ioo 0 (bb i) := by
  have hc0 : m.cost < bb 0 := lt_of_lt_of_le hcb (min_le_left _ _)
  have hc1 : m.cost < bb 1 := lt_of_lt_of_le hcb (min_le_right _ _)
  have hcbi : ∀ i, m.cost < bb i := by rw [Fin.forall_fin_two]; exact ⟨hc0, hc1⟩
  refine ⟨fun i => ⟨by rw [hbi]; linarith [hbb i], by rw [hbi]; linarith [hcbi i]⟩,
    min (bb 0 - m.cost) (bb 1 - m.cost) / 4,
    by have := lt_min (sub_pos.mpr hc0) (sub_pos.mpr hc1); positivity, ?_⟩
  have hηle : ∀ i, min (bb 0 - m.cost) (bb 1 - m.cost) / 4 ≤ (bb i - m.cost) / 4 := by
    rw [Fin.forall_fin_two]
    exact ⟨by linarith [min_le_left (bb 0 - m.cost) (bb 1 - m.cost)],
      by linarith [min_le_right (bb 0 - m.cost) (bb 1 - m.cost)]⟩
  intro i x hx
  have := hηle i; have := hbi i; have := hbb i; have := hcbi i
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem ub_local_cont {f g : ℝ → ℝ} {a lo hi : ℝ} (hsub : Set.Icc lo hi ⊆ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : Continuous g) :
    ContinuousOn f (Set.Icc lo hi) :=
  hg.continuousOn.congr (fun y hy => heq y (hsub hy))

theorem ub_surplus_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : surplus m i p = (bb i - p) ^ 2 / (2 * bb i) := by
  unfold surplus; rw [hlaw i]; exact uniform_surplus (hbb i) hp hpb

end CohenPriceFairness.LocalWelfare.Sol_uniform_surplus_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_surplus_claim

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .surplus (fun D => D < 0) := by
  obtain ⟨hiff, hreg⟩ := uniform_profit_regular m hd hc bb hbb hcb hlaw
  obtain ⟨-, -, -, -, hSd, hdem⟩ := hreg b hb
  have hbi := (hiff b).1 hb
  obtain ⟨hmem, η, hη, hsub⟩ := ub_nbhd m hc bb hbb hcb b hbi
  have hc0 : m.cost < bb 0 := lt_of_lt_of_le hcb (min_le_left _ _)
  have hc1 : m.cost < bb 1 := lt_of_lt_of_le hcb (min_le_right _ _)
  have hp0 := hbi 0
  have hp1 := hbi 1
  have hb0 := hbb 0
  have hb1 := hbb 1
  have hne' : bb 0 - bb 1 ≠ 0 := sub_ne_zero.mpr hne
  have hSloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), surplus m i y = (bb i - y) ^ 2 / (2 * bb i) :=
    fun i y hy => ub_surplus_in m bb hbb hlaw i hy.1.le hy.2.le
  have hGs : (bb 0 - (bb 0 + m.cost) / 2) ^ 2 / (2 * bb 0) -
      (bb 1 - (bb 1 + m.cost) / 2) ^ 2 / (2 * bb 1) =
      (bb 0 - bb 1) * (bb 0 * bb 1 - m.cost ^ 2) / (8 * bb 0 * bb 1) := by
    field_simp; ring
  have hcc : m.cost ^ 2 < bb 0 * bb 1 := by
    have := mul_lt_mul'' hc0 hc1 hc hc; nlinarith
  have hGs0 : (bb 0 - bb 1) * (bb 0 * bb 1 - m.cost ^ 2) / (8 * bb 0 * bb 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero hne' (sub_pos.mpr hcc).ne') (by positivity)
  refine ub_main m hd hc bb hbb hcb hlaw b hb .surplus _ (fun i => -demand m i (b i))
    ⟨η, hη, fun i => ub_local_cont (hsub i) (hSloc i) (by fun_prop)⟩ hSd ?_ ?_ (fun S hS => ?_)
  · rw [hdem 0]
    have : 0 < (bb 0 - m.cost) / (2 * bb 0) := div_pos (sub_pos.mpr hc0) (by positivity)
    exact neg_ne_zero.mpr this.ne'
  · show surplus m 0 (b 0) ≠ surplus m 1 (b 1)
    rw [hSloc 0 _ (hmem 0), hSloc 1 _ (hmem 1), hp0, hp1]
    intro h; apply hGs0; rw [← hGs, h, sub_self]
  · show -((surplus m 0 (b 0) - surplus m 1 (b 1)) *
      ((bb 0 - b 0) * -demand m 0 (b 0) - (bb 1 - b 1) * -demand m 1 (b 1))) / S / 2 < 0
    rw [hSloc 0 _ (hmem 0), hSloc 1 _ (hmem 1), hdem 0, hdem 1, hp0, hp1]
    have e : (bb 0 - (bb 0 + m.cost) / 2) * -((bb 0 - m.cost) / (2 * bb 0)) -
        (bb 1 - (bb 1 + m.cost) / 2) * -((bb 1 - m.cost) / (2 * bb 1)) =
        -2 * ((bb 0 - (bb 0 + m.cost) / 2) ^ 2 / (2 * bb 0) -
          (bb 1 - (bb 1 + m.cost) / 2) ^ 2 / (2 * bb 1)) := by
      field_simp; ring
    rw [e, hGs]
    generalize (bb 0 - bb 1) * (bb 0 * bb 1 - m.cost ^ 2) / (8 * bb 0 * bb 1) = G at hGs0 ⊢
    have := sq_pos_of_ne_zero hGs0
    have h2 : -(G * (-2 * G)) = 2 * G ^ 2 := by ring
    rw [h2]
    exact div_neg_of_neg_of_pos (div_neg_of_pos_of_neg (by positivity) hS) two_pos
