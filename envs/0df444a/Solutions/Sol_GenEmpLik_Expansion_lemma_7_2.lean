-- Prove2me | solution 2 for GenEmpLik.Expansion.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T19:08:59.676957+00:00
-- url     : https://prove2.me/submissions/581c72fc-9d55-4246-8c8d-55e27864f88d

import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Topology


private lemma running_max_tendsto {a : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ n, 0 ≤ a n)
    (hsmall : ∀ m : ℕ, ∀ᶠ n in atTop,
      a n < (1 / ((m : ℝ) + 1)) * ((n : ℝ) + 1) ^ r) :
    Tendsto (fun n : ℕ => (⨆ i : Fin n, a i) / (n : ℝ) ^ r) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmall m)
  let B : ℝ := ∑ i ∈ Finset.range N, a i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => ha i)
  have hlim : Tendsto (fun n : ℕ => B / (n : ℝ) ^ r) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).const_div_atTop B
  obtain ⟨N', hN'⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 (ε / 2) (half_pos hε))
  refine ⟨max (max N N') 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  let : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have hpow : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) r
  have hsup_nonneg : 0 ≤ ⨆ i : Fin n, a i :=
    le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hnpos⟩ (ha 0)
  have hsup : (⨆ i : Fin n, a i) ≤ B + (1 / ((m : ℝ) + 1)) * (n : ℝ) ^ r := by
    refine ciSup_le fun i => ?_
    by_cases hi : N ≤ i.val
    · have hidx : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hp : ((i.val : ℝ) + 1) ^ r ≤ (n : ℝ) ^ r :=
        Real.rpow_le_rpow (by positivity) hidx hr.le
      exact ((hN _ hi).le.trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans
        (le_add_of_nonneg_left hB)
    · exact (Finset.single_le_sum (fun j _ => ha j)
        (Finset.mem_range.mpr (not_le.mp hi))).trans (le_add_of_nonneg_right (by positivity))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsup_nonneg hpow.le)]
  have hdiv : (⨆ i : Fin n, a i) / (n : ℝ) ^ r ≤ B / (n : ℝ) ^ r + 1 / ((m : ℝ) + 1) := by
    simpa only [add_div, mul_div_cancel_right₀ _ hpow.ne'] using
      div_le_div_of_nonneg_right hsup hpow.le
  linarith [hN' n ((le_max_right N N').trans ((le_max_left _ _).trans hn))]

private lemma moment_tail_summable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {k : ℝ} (hk : 0 < k)
    (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) (ε : ℝ) (hε : 0 < ε) :
    (∑' m : ℕ, P {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) ≠ ⊤ := by
  let Y : ℕ → Ω → ℝ := fun m ω => |Z m ω| ^ k / ε ^ k
  have hYint : Integrable (Y 0) P := hmom.div_const (ε ^ k)
  have hYnonneg : ∀ m ω, 0 ≤ Y m ω := fun m ω =>
    div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hε.le _)
  have hmeas : Measurable (fun u : ℝ => |u| ^ k / ε ^ k) :=
    ((continuous_abs.rpow_const (fun _ => Or.inr hk.le)).div_const _).measurable
  have hYident : ∀ m, IdentDistrib (Y m) (Y 0) P P := fun m => (hident m).comp hmeas
  have heq : ∀ m : ℕ, P {ω | (m : ℝ) < Y m ω} = P {ω | (m : ℝ) < Y 0 ω} :=
    fun m => (hYident m).measure_mem_eq measurableSet_Ioi
  have hsum : (∑' m : ℕ, P {ω | (m : ℝ) < Y m ω}) < ⊤ := by
    let : MeasureSpace Ω := ⟨P⟩
    calc
      _ = ∑' m : ℕ, P {ω | (m : ℝ) < Y 0 ω} := tsum_congr heq
      _ < ⊤ := tsum_prob_mem_Ioi_lt_top hYint (hYnonneg 0)
  have hsub : ∀ m : ℕ, {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|} ⊆
      {ω | (m : ℝ) < Y m ω} := by
    intro m ω hω
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ ε * ((m : ℝ) + 1) ^ (1 / k)) hω hk.le
    rw [Real.mul_rpow hε.le (by positivity), one_div,
      Real.rpow_inv_rpow (by positivity) hk.ne'] at hpow
    exact (lt_add_one (m : ℝ)).trans_le
      ((le_div_iff₀ (Real.rpow_pos_of_pos hε k)).mpr (by simpa only [mul_comm] using hpow))
  exact ne_top_of_le_ne_top hsum.ne (ENNReal.tsum_le_tsum fun m => measure_mono (hsub m))

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) {k : ℝ} (hk : 0 < k)
    (hmom : Integrable (fun ω => |Z 0 ω| ^ k) P) :
    (∀ ε : ℝ, 0 < ε →
      P (limsup (fun m : ℕ => {ω | ε * ((m : ℝ) + 1) ^ (1 / k) ≤ |Z m ω|}) atTop) = 0) ∧
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Z i ω|) / (n : ℝ) ^ (1 / k))
      atTop (𝓝 0)) := by
  refine ⟨fun ε hε => measure_limsup_atTop_eq_zero
    (moment_tail_summable Z hident hk hmom ε hε), ?_⟩
  have hcount : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |Z n ω| < (1 / ((m : ℝ) + 1)) * ((n : ℝ) + 1) ^ (1 / k) := fun m =>
    (ae_eventually_notMem (moment_tail_summable Z hident hk hmom (1 / ((m : ℝ) + 1))
      (by positivity))).mono fun ω hω => hω.mono fun n hn => lt_of_not_ge hn
  filter_upwards [ae_all_iff.mpr hcount] with ω hω
  exact running_max_tendsto (one_div_pos.mpr hk) (fun n => abs_nonneg _) hω
