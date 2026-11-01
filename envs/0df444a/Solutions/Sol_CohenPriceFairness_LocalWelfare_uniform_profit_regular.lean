-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_profit_regular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:47.068836+00:00
-- url     : https://prove2.me/submissions/2f9c050a-427f-46dc-b4cf-c2d5b5283786

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_surplus

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_profit_regular

open CohenPriceFairness.LocalWelfare

theorem ub_demand (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p) :
    demand m i p = max 0 (1 - p / bb i) := by
  unfold demand; rw [hlaw i]; exact uniform_demand (hbb i) hp

theorem ub_demand_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : demand m i p = 1 - p / bb i := by
  rw [ub_demand m bb hbb hlaw i hp]
  apply max_eq_right
  rw [sub_nonneg, div_le_one (hbb i)]; exact hpb

theorem ub_profit_ge (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ}
    (hpb : bb i ≤ p) : profit m i p = 0 := by
  unfold profit
  rw [ub_demand m bb hbb hlaw i (le_trans (hbb i).le hpb), max_eq_left]
  · ring
  · rw [sub_nonpos, one_le_div (hbb i)]; exact hpb

theorem ub_quad (d c B p : ℝ) (hB : 0 < B) :
    d * (p - c) * (1 - p / B) = d * (B - c) ^ 2 / (4 * B) - d / B * (p - (B + c) / 2) ^ 2 := by
  field_simp; ring

theorem ub_profit_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : profit m i p = m.population i * (bb i - m.cost) ^ 2 / (4 * bb i) -
      m.population i / bb i * (p - (bb i + m.cost) / 2) ^ 2 := by
  unfold profit; rw [ub_demand_in m bb hbb hlaw i hp hpb, ub_quad _ _ _ _ (hbb i)]

theorem ub_surplus_in (m : Market) (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i)
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) (i : Fin 2) {p : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ bb i) : surplus m i p = (bb i - p) ^ 2 / (2 * bb i) := by
  unfold surplus; rw [hlaw i]; exact uniform_surplus (hbb i) hp hpb

theorem ub_local_deriv {f g : ℝ → ℝ} {a x g' : ℝ} (hx : x ∈ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : HasDerivAt g g' x) : HasDerivAt f g' x :=
  hg.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) heq)

theorem ub_local_cont {f g : ℝ → ℝ} {a lo hi : ℝ} (hsub : Set.Icc lo hi ⊆ Set.Ioo 0 a)
    (heq : ∀ y ∈ Set.Ioo 0 a, f y = g y) (hg : Continuous g) :
    ContinuousOn f (Set.Icc lo hi) :=
  hg.continuousOn.congr (fun y hy => heq y (hsub hy))

end CohenPriceFairness.LocalWelfare.Sol_uniform_profit_regular

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_profit_regular
open Filter Topology Asymptotics

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hcb : m.cost < min (bb 0) (bb 1))
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) :
    (∀ b : Prices, BaselineOptimal m b ↔ ∀ i, b i = (bb i + m.cost) / 2) ∧
    ∀ b : Prices, BaselineOptimal m b →
      (∀ i, 0 < b i) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε) ∧
      (∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η))) ∧
      (∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - (-2 * m.population i / bb i) / 2 * h ^ 2)
        =o[𝓝 0] (fun h => h ^ 2)) ∧
      (∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i)) ∧
      (∀ i, demand m i (b i) = (bb i - m.cost) / (2 * bb i)) := by
  have hc0 : m.cost < bb 0 := lt_of_lt_of_le hcb (min_le_left _ _)
  have hc1 : m.cost < bb 1 := lt_of_lt_of_le hcb (min_le_right _ _)
  have hcbi : ∀ i, m.cost < bb i := by rw [Fin.forall_fin_two]; exact ⟨hc0, hc1⟩
  obtain ⟨ps, hps⟩ : ∃ ps : Prices, ps = fun i => (bb i + m.cost) / 2 := ⟨_, rfl⟩
  have hpsi : ∀ i, ps i = (bb i + m.cost) / 2 := fun i => by rw [hps]
  have hps_pos : ∀ i, 0 < ps i := fun i => by rw [hpsi]; linarith [hbb i]
  have hps_lt : ∀ i, ps i < bb i := fun i => by rw [hpsi]; linarith [hcbi i]
  obtain ⟨A, hA⟩ : ∃ A : Fin 2 → ℝ,
      A = fun i => m.population i * (bb i - m.cost) ^ 2 / (4 * bb i) := ⟨_, rfl⟩
  have hApos : ∀ i, 0 < A i := fun i => by
    have := sub_pos.mpr (hcbi i); have := hd i; have := hbb i; rw [hA]; positivity
  have hkpos : ∀ i, 0 < m.population i / bb i := fun i => div_pos (hd i) (hbb i)
  have hRin : ∀ i p, 0 ≤ p → p ≤ bb i →
      profit m i p = A i - m.population i / bb i * (p - ps i) ^ 2 := by
    intro i p hp hpb; rw [ub_profit_in m bb hbb hlaw i hp hpb, hpsi, hA]
  have hRs : ∀ i, profit m i (ps i) = A i := by
    intro i; rw [hRin i _ (hps_pos i).le (hps_lt i).le]; ring
  have hRge : ∀ i p, bb i ≤ p → profit m i p = 0 := fun i p h => ub_profit_ge m bb hbb hlaw i h
  have hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (ps i) := by
    intro i p hp
    rw [hRs]
    rcases le_or_gt p (bb i) with h | h
    · rw [hRin i p hp h]
      have := mul_nonneg (hkpos i).le (sq_nonneg (p - ps i))
      linarith
    · rw [hRge i p h.le]; exact (hApos i).le
  have hBOps : BaselineOptimal m ps := fun i => ⟨(hps_pos i).le, hopt i⟩
  have huniq : ∀ b : Prices, BaselineOptimal m b → b = ps := by
    intro b hb
    funext i
    obtain ⟨hb0, hbm⟩ := hb i
    have h := hbm (ps i) (hps_pos i).le
    rw [hRs] at h
    rcases le_or_gt (b i) (bb i) with h' | h'
    · rw [hRin i _ hb0 h'] at h
      have hx : (b i - ps i) ^ 2 ≤ 0 := by
        by_contra hx; push Not at hx; have := mul_pos (hkpos i) hx; linarith
      have := le_antisymm hx (sq_nonneg _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)
    · rw [hRge i _ h'.le] at h; linarith [hApos i]
  have hiff : ∀ b : Prices, BaselineOptimal m b ↔ ∀ i, b i = (bb i + m.cost) / 2 := by
    intro b
    constructor
    · intro hb i; rw [huniq b hb, hpsi]
    · intro hb
      have : b = ps := funext fun i => by rw [hb i, hpsi]
      rw [this]; exact hBOps
  refine ⟨hiff, ?_⟩
  intro b hb
  have hbps := huniq b hb
  subst b
  have hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (ps i) - δ ≤ profit m i p →
      |p - ps i| < ε := by
    intro ε hε
    have key : ∀ i, ∃ δ > 0, ∀ p, 0 ≤ p → profit m i (ps i) - δ ≤ profit m i p →
        |p - ps i| < ε := by
      intro i
      have hk := hkpos i
      refine ⟨min (A i / 2) (m.population i / bb i * ε ^ 2 / 2),
        lt_min (by linarith [hApos i]) (by positivity), ?_⟩
      intro p hp hle
      have hm1 := min_le_left (A i / 2) (m.population i / bb i * ε ^ 2 / 2)
      have hm2 := min_le_right (A i / 2) (m.population i / bb i * ε ^ 2 / 2)
      rw [hRs] at hle
      rcases le_or_gt p (bb i) with h | h
      · rw [hRin i p hp h] at hle
        apply abs_lt_of_sq_lt_sq _ hε.le
        by_contra hx; push Not at hx
        have := mul_le_mul_of_nonneg_left hx hk.le
        have := mul_pos hk (pow_pos hε 2)
        linarith
      · rw [hRge i p h.le] at hle; linarith [hApos i]
    obtain ⟨δ0, hδ0, H0⟩ := key 0
    obtain ⟨δ1, hδ1, H1⟩ := key 1
    refine ⟨min δ0 δ1, lt_min hδ0 hδ1, ?_⟩
    rw [Fin.forall_fin_two]
    exact ⟨fun p hp hle => H0 p hp (by linarith [min_le_left δ0 δ1]),
      fun p hp hle => H1 p hp (by linarith [min_le_right δ0 δ1])⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (bb 0 - m.cost) (bb 1 - m.cost) / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hη]; have := lt_min (sub_pos.mpr hc0) (sub_pos.mpr hc1); positivity
  have hηle : ∀ i, η ≤ (bb i - m.cost) / 4 := by
    rw [Fin.forall_fin_two, hη]
    exact ⟨by linarith [min_le_left (bb 0 - m.cost) (bb 1 - m.cost)],
      by linarith [min_le_right (bb 0 - m.cost) (bb 1 - m.cost)]⟩
  have hsub : ∀ i, Set.Icc (ps i - η) (ps i + η) ⊆ Set.Ioo 0 (bb i) := by
    intro i x hx
    have := hηle i; have := hpsi i; have := hbb i; have := hcbi i
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmem : ∀ i, ps i ∈ Set.Ioo 0 (bb i) := fun i => ⟨hps_pos i, hps_lt i⟩
  have hRloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i),
      profit m i y = A i - m.population i / bb i * (y - ps i) ^ 2 :=
    fun i y hy => hRin i y hy.1.le hy.2.le
  have hcontR : ∀ i, ContinuousOn (profit m i) (Set.Icc (ps i - η) (ps i + η)) :=
    fun i => ub_local_cont (hsub i) (hRloc i) (by fun_prop)
  have hRt : ∀ i, (fun h => profit m i (ps i + h) - profit m i (ps i) -
      (-2 * m.population i / bb i) / 2 * h ^ 2) =o[𝓝 0] (fun h => h ^ 2) := by
    intro i
    refine (isLittleO_zero (fun h : ℝ => h ^ 2) (𝓝 0)).congr' ?_ EventuallyEq.rfl
    have hmem' : Set.Ioo (-ps i) (bb i - ps i) ∈ 𝓝 (0:ℝ) :=
      Ioo_mem_nhds (by linarith [hps_pos i]) (by linarith [hps_lt i])
    filter_upwards [hmem'] with h hh
    rw [hRloc i _ ⟨by linarith [hh.1], by linarith [hh.2]⟩, hRs]
    ring
  have hSloc : ∀ i, ∀ y ∈ Set.Ioo 0 (bb i), surplus m i y = (bb i - y) ^ 2 / (2 * bb i) :=
    fun i y hy => ub_surplus_in m bb hbb hlaw i hy.1.le hy.2.le
  have hdemv : ∀ i, demand m i (ps i) = 1 - ps i / bb i :=
    fun i => ub_demand_in m bb hbb hlaw i (hps_pos i).le (hps_lt i).le
  have hSd : ∀ i, HasDerivAt (surplus m i) (-demand m i (ps i)) (ps i) := by
    intro i
    apply ub_local_deriv (hmem i) (hSloc i)
    have h1 : HasDerivAt (fun y => bb i - y) (-1) (ps i) :=
      (hasDerivAt_id' (ps i)).const_sub (bb i)
    refine ((h1.fun_pow 2).div_const (2 * bb i)).congr_deriv ?_
    rw [hdemv i]
    have := (hbb i).ne'
    field_simp
    norm_num
    ring
  refine ⟨hps_pos, hloc, ⟨η, hηpos, hcontR⟩, hRt, hSd, fun i => ?_⟩
  rw [hdemv i, hpsi i]
  have := (hbb i).ne'
  field_simp
  ring
