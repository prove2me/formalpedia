-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_demand_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:56.447915+00:00
-- url     : https://prove2.me/submissions/c12943ba-0d51-4e3c-8d1e-53b7d5ff0f8c

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim

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

theorem ub_local_deriv {f g : ℝ → ℝ} {a x g' : ℝ} (hx : x ∈ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : HasDerivAt g g' x) : HasDerivAt f g' x :=
  hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) heq)

theorem ub_local_cont {f g : ℝ → ℝ} {a lo hi : ℝ} (hsub : Set.Icc lo hi ⊆ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : Continuous g) :
    ContinuousOn f (Set.Icc lo hi) :=
  hg.continuousOn.congr (fun y hy => heq y (hsub hy))

theorem ub_demand_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : demand m i p = 1 - p / bb i := by
  unfold demand; rw [hlaw i, uniform_demand (hbb i) hp]
  apply max_eq_right
  rw [sub_nonneg, div_le_one (hbb i)]; exact hpb

end CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 < m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .demand (fun D => D < 0) := by
  have hbi := ((uniform_profit_regular m hd hc.le bb hbb hcb hlaw).1 b).1 hb
  obtain ⟨hmem, η, hη, hsub⟩ := ub_nbhd m hc.le bb hbb hcb b hbi
  have hp0 := hbi 0
  have hp1 := hbi 1
  have hb0 := hbb 0
  have hb1 := hbb 1
  have hne' : bb 0 - bb 1 ≠ 0 := sub_ne_zero.mpr hne
  have hDloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), demand m i y = 1 - y / bb i :=
    fun i y hy => ub_demand_in m bb hbb hlaw i hy.1.le hy.2.le
  have hGd : (1 - b 0 / bb 0) - (1 - b 1 / bb 1) =
      m.cost * (bb 0 - bb 1) / (2 * bb 0 * bb 1) := by
    rw [hp0, hp1]; field_simp; ring
  have hGd0 : m.cost * (bb 0 - bb 1) / (2 * bb 0 * bb 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero hc.ne' hne') (by positivity)
  refine ub_main m hd hc.le bb hbb hcb hlaw b hb .demand _ (fun i => -(1 / bb i))
    ⟨η, hη, fun i => ub_local_cont (hsub i) (hDloc i) (by fun_prop)⟩
    (fun i => ub_local_deriv (hmem i) (hDloc i)
      (((hasDerivAt_id (b i)).div_const (bb i)).const_sub 1))
    (neg_ne_zero.mpr (one_div_ne_zero hb0.ne')) ?_ (fun S hS => ?_)
  · show demand m 0 (b 0) ≠ demand m 1 (b 1)
    rw [hDloc 0 _ (hmem 0), hDloc 1 _ (hmem 1)]
    intro h; apply hGd0; rw [← hGd, h, sub_self]
  · show -((demand m 0 (b 0) - demand m 1 (b 1)) *
      ((bb 0 - b 0) * -(1 / bb 0) - (bb 1 - b 1) * -(1 / bb 1))) / S / 2 < 0
    rw [hDloc 0 _ (hmem 0), hDloc 1 _ (hmem 1)]
    have e : (bb 0 - b 0) * -(1 / bb 0) - (bb 1 - b 1) * -(1 / bb 1) =
        -((1 - b 0 / bb 0) - (1 - b 1 / bb 1)) := by field_simp; ring
    rw [e, hGd]
    generalize m.cost * (bb 0 - bb 1) / (2 * bb 0 * bb 1) = G at hGd0 ⊢
    have := sq_pos_of_ne_zero hGd0
    have h2 : -(G * -G) = G ^ 2 := by ring
    rw [h2]
    exact div_neg_of_neg_of_pos (div_neg_of_pos_of_neg this hS) two_pos
