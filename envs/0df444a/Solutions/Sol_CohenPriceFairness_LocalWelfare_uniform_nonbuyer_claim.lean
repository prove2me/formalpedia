-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_nonbuyer_claim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:53.283266+00:00
-- url     : https://prove2.me/submissions/b44e73f1-ceca-45f9-bf69-5cbf33cbb53f

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_nonbuyer

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_nonbuyer_claim

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

theorem ub_nonbuyer_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 < p)
    (hpb : p ≤ bb i) : nonbuyer m i p = p / 2 := by
  unfold nonbuyer; rw [hlaw i]; exact uniform_nonbuyer (hbb i) hp hpb

end CohenPriceFairness.LocalWelfare.Sol_uniform_nonbuyer_claim

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_nonbuyer_claim

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .nonbuyer (fun D => 0 < D) := by
  have hbi := ((uniform_profit_regular m hd hc bb hbb hcb hlaw).1 b).1 hb
  obtain ⟨hmem, η, hη, hsub⟩ := ub_nbhd m hc bb hbb hcb b hbi
  have hp0 := hbi 0
  have hp1 := hbi 1
  have hne' : bb 0 - bb 1 ≠ 0 := sub_ne_zero.mpr hne
  have hNloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), nonbuyer m i y = y / 2 :=
    fun i y hy => ub_nonbuyer_in m bb hbb hlaw i hy.1 hy.2.le
  refine ub_main m hd hc bb hbb hcb hlaw b hb .nonbuyer _ (fun _ => 1 / 2)
    ⟨η, hη, fun i => ub_local_cont (hsub i) (hNloc i) (by fun_prop)⟩
    (fun i => ub_local_deriv (hmem i) (hNloc i) ((hasDerivAt_id (b i)).div_const 2))
    (by norm_num) ?_ (fun S hS => ?_)
  · show nonbuyer m 0 (b 0) ≠ nonbuyer m 1 (b 1)
    rw [hNloc 0 _ (hmem 0), hNloc 1 _ (hmem 1), hp0, hp1]; intro h; apply hne; linarith
  · show 0 < -((nonbuyer m 0 (b 0) - nonbuyer m 1 (b 1)) *
      ((bb 0 - b 0) * (1 / 2) - (bb 1 - b 1) * (1 / 2))) / S / 2
    rw [hNloc 0 _ (hmem 0), hNloc 1 _ (hmem 1), hp0, hp1]
    have e : ((bb 0 + m.cost) / 2 / 2 - (bb 1 + m.cost) / 2 / 2) *
        ((bb 0 - (bb 0 + m.cost) / 2) * (1 / 2) - (bb 1 - (bb 1 + m.cost) / 2) * (1 / 2)) =
        (bb 0 - bb 1) ^ 2 / 16 := by ring
    rw [e]
    have := sq_pos_of_ne_zero hne'
    exact half_pos (div_pos_of_neg_of_neg (by linarith) hS)
