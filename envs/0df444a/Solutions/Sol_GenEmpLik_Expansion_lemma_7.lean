-- Prove2me | solution 1 for GenEmpLik.Expansion.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T08:06:24.386013+00:00
-- url     : https://prove2.me/submissions/9bad011a-1839-417e-9e76-0fec7f792779

import Mathlib

namespace Prove2SwarmSubmission

set_option autoImplicit false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GenEmpLik.Expansion

lemma rpow_event_iff {ε k a x : ℝ} (hε : 0 < ε) (hk : 0 < k) (ha : 0 ≤ a) :
    ε * a ^ (1 / k) ≤ |x| ↔ a ≤ |x| ^ k / ε ^ k := by
  have hpow_left : (ε * a ^ (1 / k)) ^ k = a * ε ^ k := by
    calc
      (ε * a ^ (1 / k)) ^ k = ε ^ k * (a ^ (1 / k)) ^ k := by
        rw [Real.mul_rpow hε.le (Real.rpow_nonneg ha _)]
      _ = ε ^ k * a := by
        rw [show (a ^ (1 / k)) ^ k = a by
          simpa [one_div] using Real.rpow_inv_rpow ha hk.ne']
      _ = a * ε ^ k := by ring
  calc
    ε * a ^ (1 / k) ≤ |x| ↔ (ε * a ^ (1 / k)) ^ k ≤ |x| ^ k :=
      (Real.rpow_le_rpow_iff (mul_nonneg hε.le (Real.rpow_nonneg ha _)) (abs_nonneg x) hk).symm
    _ ↔ a * ε ^ k ≤ |x| ^ k := by rw [hpow_left]
    _ ↔ a ≤ |x| ^ k / ε ^ k := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hε k)]

end GenEmpLik.Expansion

namespace GenEmpLik.Expansion

lemma conjunct1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    {k : ℝ} (hk : 0 < k) (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    ∀ ε : ℝ, 0 < ε →
      P (limsup (fun m : ℕ => {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop) = 0 := by
  intro ε hε
  letI : MeasureSpace Ω := ⟨P⟩
  have hprob : IsProbabilityMeasure (ℙ : Measure Ω) := by
    change IsProbabilityMeasure P
    infer_instance
  let W : Ω → ℝ := fun ω => |Z 0 ω| ^ k / ε ^ k
  have hWint : Integrable W P := by
    simpa [W] using hmom.div_const (ε ^ k)
  have hWnonneg : 0 ≤ W := by
    intro ω
    exact div_nonneg (Real.rpow_nonneg (abs_nonneg (Z 0 ω)) k)
      (Real.rpow_pos_of_pos hε k).le
  have htsumW : (∑' j : ℕ, P {ω | W ω ∈ Set.Ioi (j : ℝ)}) < ∞ := by
    have h := ProbabilityTheory.tsum_prob_mem_Ioi_lt_top (X := W) hWint hWnonneg
    change (∑' j : ℕ, P {ω | W ω ∈ Set.Ioi (j : ℝ)}) < ∞ at h
    exact h
  refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top htsumW.ne ?_)
  apply ENNReal.tsum_le_tsum
  intro m
  have hmeas : MeasurableSet {x : ℝ | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |x|} :=
    measurableSet_le measurable_const measurable_abs
  calc
    P {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}
        = P {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z 0 ω|} := by
          simpa using (hident m).measure_mem_eq hmeas
    _ = P {ω | ((m : ℝ) + 1) ≤ W ω} := by
          congr 1
          ext ω
          simpa [W] using (rpow_event_iff (x := Z 0 ω) hε hk (show 0 ≤ (m : ℝ) + 1 by positivity))
    _ ≤ P {ω | W ω ∈ Set.Ioi (m : ℝ)} := by
          apply measure_mono
          intro ω hω
          exact lt_of_lt_of_le (lt_add_one (m : ℝ)) hω

end GenEmpLik.Expansion

namespace GenEmpLik.Expansion

lemma tendsto_of_eventually_lt_zero {q : ℕ → ℝ} (hq_nonneg : ∀ n, 0 ≤ q n)
    (hq : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, q n < δ) :
    Tendsto q atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with n
    exact ha.trans_le (hq_nonneg n)
  · exact hq

lemma deterministic_running_max
    (x : ℕ → ℝ) (hx_nonneg : ∀ m, 0 ≤ x m) {k : ℝ} (hk : 0 < k)
    (hsmall : ∀ j : ℕ, ∀ᶠ m : ℕ in atTop,
      x m < (1 / ((j : ℝ) + 1)) * ((m : ℝ) + 1) ^ (1 / k)) :
    Tendsto (fun n : ℕ => (⨆ i : Fin n, x i) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / k)) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr hk)).comp tendsto_natCast_atTop_atTop
  refine tendsto_of_eventually_lt_zero (fun n => ?_) ?_
  · exact div_nonneg (Real.iSup_nonneg (fun i : Fin n => hx_nonneg i))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro δ hδ
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < δ / 2 by positivity)
    rcases (eventually_atTop.mp (hsmall j)) with ⟨M, hM⟩
    let C : ℝ := ⨆ i : Fin M, x i
    have hC_nonneg : 0 ≤ C := Real.iSup_nonneg (fun i : Fin M => hx_nonneg i)
    have hCdiv : Tendsto (fun n : ℕ => C / (n : ℝ) ^ (1 / k)) atTop (𝓝 0) :=
      hden.const_div_atTop C
    have hCdiv_ev : ∀ᶠ n : ℕ in atTop, C / (n : ℝ) ^ (1 / k) < δ / 2 :=
      (tendsto_order.mp hCdiv).2 (δ / 2) (by positivity)
    filter_upwards [hCdiv_ev, eventually_ge_atTop (M + 1)] with n hnC hnM
    have hnpos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ M) hnM
    have hdenpos : 0 < (n : ℝ) ^ (1 / k) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
    have hbdd : BddAbove (Set.range (fun i : Fin M => x i)) := Finite.bddAbove_range _
    have hmax_bound : ∀ i : Fin n,
        x i ≤ max C ((1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k)) := by
      intro i
      by_cases hiM : i.val < M
      · have hxC : x i ≤ C := by
          simpa using le_ciSup hbdd (⟨i.val, hiM⟩ : Fin M)
        exact hxC.trans (le_max_left _ _)
      · have hMi : M ≤ i.val := Nat.le_of_not_gt hiM
        have hi_lt_n : i.val < n := i.isLt
        have hi1 : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hi_lt_n
        have hrpow : ((i.val : ℝ) + 1) ^ (1 / k) ≤ (n : ℝ) ^ (1 / k) :=
          Real.rpow_le_rpow (by positivity) hi1 (one_div_pos.mpr hk).le
        have hxsmall : x i < (1 / ((j : ℝ) + 1)) * ((i.val : ℝ) + 1) ^ (1 / k) := by
          simpa using hM i.val hMi
        have hleB : x i ≤ (1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k) :=
          hxsmall.le.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))
        exact hleB.trans (le_max_right _ _)
    have hsup_bound : (⨆ i : Fin n, x i) ≤
        max C ((1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k)) :=
      Real.iSup_le hmax_bound (le_trans hC_nonneg (le_max_left _ _))
    have hdiv_bound : (⨆ i : Fin n, x i) / (n : ℝ) ^ (1 / k) ≤
        max (C / (n : ℝ) ^ (1 / k)) (1 / ((j : ℝ) + 1)) := by
      calc
        (⨆ i : Fin n, x i) / (n : ℝ) ^ (1 / k)
            ≤ max C ((1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k)) /
                (n : ℝ) ^ (1 / k) :=
              div_le_div_of_nonneg_right hsup_bound hdenpos.le
        _ = max (C / (n : ℝ) ^ (1 / k))
              (((1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k)) / (n : ℝ) ^ (1 / k)) :=
              (max_div_div_right hdenpos.le C
                ((1 / ((j : ℝ) + 1)) * (n : ℝ) ^ (1 / k))).symm
        _ = max (C / (n : ℝ) ^ (1 / k)) (1 / ((j : ℝ) + 1)) := by
              congr 1
              field_simp [hdenpos.ne']
    have hlt : max (C / (n : ℝ) ^ (1 / k)) (1 / ((j : ℝ) + 1)) < δ :=
      max_lt (hnC.trans (half_lt_self hδ)) (hj.trans (half_lt_self hδ))
    exact hdiv_bound.trans_lt hlt

end GenEmpLik.Expansion

namespace GenEmpLik.Expansion

lemma conjunct2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    {k : ℝ} (hk : 0 < k) (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ m : ℕ in atTop,
      |Z m ω| < (1 / ((j : ℝ) + 1)) * ((m : ℝ) + 1) ^ (1 / k) := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    have hε : 0 < (1 / ((j : ℝ) + 1) : ℝ) := by positivity
    have hzero := conjunct1 Z hident hk hmom (1 / ((j : ℝ) + 1)) hε
    have hnotlimsup : ∀ᵐ ω ∂P,
        ω ∉ limsup (fun m : ℕ =>
          {ω | (1 / ((j : ℝ) + 1)) * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop := by
      rw [MeasureTheory.ae_iff]
      simpa using hzero
    filter_upwards [hnotlimsup] with ω hω
    rw [Filter.mem_limsup_iff_frequently_mem] at hω
    filter_upwards [Filter.not_frequently.mp hω] with m hm
    exact not_le.mp hm
  filter_upwards [hall] with ω hω
  exact deterministic_running_max (fun m => |Z m ω|) (fun m => abs_nonneg _) hk hω

theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {k : ℝ} (hk : 0 < k)
    (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    (∀ ε : ℝ, 0 < ε →
      P (limsup (fun m : ℕ => {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop) = 0) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0)) :=
  ⟨conjunct1 Z hident hk hmom, conjunct2 Z hident hk hmom⟩

end GenEmpLik.Expansion

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter Topology
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {k : ℝ} (hk : 0 < k)
    (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    (∀ ε : ℝ, 0 < ε →
      P (limsup (fun m : ℕ => {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop) = 0) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0)) := by
  exact Prove2SwarmSubmission.GenEmpLik.Expansion.lemma_7 Z hident hk hmom
