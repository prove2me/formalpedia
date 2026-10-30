-- Prove2me | solution 1 for FragileBandit.CauchyTail.markov_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:24:49.186504+00:00
-- url     : https://prove2.me/submissions/f180edf2-7a9f-4f37-9556-c603c3e06a71

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTMarkovAux

lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_ofPred, Finset.card_filter]

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h ≤ n := by
  rw [armPullCount_eq_sum]
  calc (∑ t : Fin n, if (h t).1 = i then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> simp)
    _ = n := by simp

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount i h) := by
  have hF : Measurable (fun h : BanditHistory K n => fun t => (h t).1) := by
    rw [measurable_pi_iff]
    intro t
    exact measurable_fst.comp (measurable_pi_apply t)
  have : (fun h : BanditHistory K n => armPullCount i h) =
      (fun a : Fin n → Fin K => ∑ t : Fin n, if a t = i then 1 else 0) ∘
        (fun h : BanditHistory K n => fun t => (h t).1) := by
    funext h; simp [armPullCount_eq_sum]
  rw [this]
  exact (measurable_of_countable _).comp hF

end CTMarkovAux

open CTMarkovAux in
theorem solution {K : ℕ} (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : (0 : ℝ) ∈ interior (natParamSet P)) (π : BanditPolicy K) (hπ : IsOptimized P π)
    (ν : StochasticBandit K) (hν : IsModelEnv P ν) (hd : DistinctMeans ν)
    (i : Fin K) (hi : 0 < banditGap ν i) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 < c) :
    ∀ a : ℝ, a < 1 → ∀ᶠ T : ℕ in atTop,
      banditMeasure ν π T {h | c * (T : ℝ) ^ γ < (armPullCount i h : ℝ)} ≤
        ENNReal.ofReal (((T : ℝ) ^ γ) ^ (-a)) := by
  intro a ha
  obtain ⟨hγ0, hγ1⟩ := hγ
  set L : ℝ := 1 / (dP P (banditArmMean ν i) (banditOptimalMean ν)).toReal with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hlim := hπ ν hν hd i hi
  rw [← hLdef] at hlim
  -- eventually E[N] / log T ≤ L + 1
  have h1 : ∀ᶠ T : ℕ in atTop, expPulls ν π T i / Real.log T ≤ L + 1 :=
    hlim.eventually (ge_mem_nhds (by linarith))
  set B : ℝ := L + 1 with hB
  have hBpos : 0 < B := by linarith
  -- log x = o(x^r) with r = γ (1 - a)
  set r : ℝ := γ * (1 - a) with hr
  have hrpos : 0 < r := mul_pos hγ0 (by linarith)
  have hlo := (isLittleO_log_rpow_atTop hrpos).bound (c := c / B) (by positivity)
  have h2 : ∀ᶠ T : ℕ in atTop, ‖Real.log (T : ℝ)‖ ≤ c / B * ‖(T : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually hlo
  have h3 : ∀ᶠ T : ℕ in atTop, (2 : ℕ) ≤ T := eventually_ge_atTop 2
  filter_upwards [h1, h2, h3] with T hT1 hT2 hT3
  have hTpos : (0 : ℝ) < T := by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT3
    linarith
  have hlogpos : 0 < Real.log (T : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ T := by exact_mod_cast hT3
    linarith)
  have hE : expPulls ν π T i ≤ B * Real.log T := by
    rwa [div_le_iff₀ hlogpos] at hT1
  have hlogle : B * Real.log T ≤ c * (T : ℝ) ^ r := by
    rw [Real.norm_of_nonneg hlogpos.le, Real.norm_of_nonneg (by positivity)] at hT2
    have := mul_le_mul_of_nonneg_left hT2 hBpos.le
    calc B * Real.log T ≤ B * (c / B * (T : ℝ) ^ r) := this
      _ = c * (T : ℝ) ^ r := by field_simp
  -- Markov
  set f : BanditHistory K T → ℝ := fun h => (armPullCount i h : ℝ)
  have hfm : Measurable f := (measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (measurable_armPullCount i)
  have hfint : Integrable f (banditMeasure ν π T) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (T : ℝ) (Filter.Eventually.of_forall ?_)
    intro h
    simp only [f, Real.norm_natCast]
    exact_mod_cast armPullCount_le i h
  set ε : ℝ := c * (T : ℝ) ^ γ with hε
  have hεpos : 0 < ε := by positivity
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := banditMeasure ν π T)
    (Filter.Eventually.of_forall (fun h => (Nat.cast_nonneg _ : (0 : ℝ) ≤ f h))) hfint ε
  have hsub : {h : BanditHistory K T | ε < (armPullCount i h : ℝ)} ⊆ {h | ε ≤ f h} :=
    fun h hh => by simp only [Set.mem_setOf_eq, f] at hh ⊢; exact le_of_lt hh
  have hreal : (banditMeasure ν π T).real {h | ε < (armPullCount i h : ℝ)} ≤
      (T : ℝ) ^ (-(γ * a)) := by
    have hmono := measureReal_mono (μ := banditMeasure ν π T) hsub
    have hint : ∫ x, f x ∂(banditMeasure ν π T) = expPulls ν π T i := rfl
    rw [hint] at hM
    have hk : ε * (banditMeasure ν π T).real {h | ε < (armPullCount i h : ℝ)} ≤
        c * (T : ℝ) ^ r := by
      calc _ ≤ ε * (banditMeasure ν π T).real {h | ε ≤ f h} :=
            mul_le_mul_of_nonneg_left hmono hεpos.le
        _ ≤ _ := hM
        _ ≤ _ := hE
        _ ≤ _ := hlogle
    have heq : c * (T : ℝ) ^ r = ε * (T : ℝ) ^ (-(γ * a)) := by
      rw [hε, mul_assoc, ← Real.rpow_add hTpos]
      congr 2
      rw [hr]; ring
    rw [heq] at hk
    exact le_of_mul_le_mul_left hk hεpos
  rw [← Real.rpow_mul hTpos.le]
  have hfin : banditMeasure ν π T {h | ε < (armPullCount i h : ℝ)} =
      ENNReal.ofReal ((banditMeasure ν π T).real {h | ε < (armPullCount i h : ℝ)}) := by
    rw [ofReal_measureReal]
  rw [hfin]
  apply ENNReal.ofReal_le_ofReal
  calc _ ≤ (T : ℝ) ^ (-(γ * a)) := hreal
    _ = (T : ℝ) ^ (γ * -a) := by ring_nf
