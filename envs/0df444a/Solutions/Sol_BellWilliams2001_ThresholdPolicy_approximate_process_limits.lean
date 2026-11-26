-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.approximate_process_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:07:38.390466+00:00
-- url     : https://prove2.me/submissions/a840521c-3e59-439c-9e9a-77731d60afc3

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

set_option maxHeartbeats 1700000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X Y : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hY : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => Y n ω t) P)
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η)
    (hA : ∀ (T : ℕ) (ε : ℝ), 0 < ε →
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε ≤ ‖Y n ω t-X n ω t‖}) atTop (𝓝 0)) :
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η) := by
  constructor
  · intro q τ hτ
    let L (n : ℕ) (ω : Ω) (j : Fin q) := Y n ω (τ j)
    let K (n : ℕ) (ω : Ω) (j : Fin q) := X n ω (τ j)
    refine tendstoInDistribution_of_tendstoInMeasure_sub (X := K) L (fun ω j => Z ω (τ j)) (hF q τ hτ) ?_
      (fun n => aemeasurable_pi_lambda _ fun j => hY n (τ j) (hτ j))
    obtain ⟨T,hT⟩ := exists_nat_gt (∑ j, τ j)
    have hbound (j : Fin q) : τ j ≤ (T:ℝ) := (Finset.single_le_sum
      (f := τ) (fun i _ => hτ i) (Finset.mem_univ j)).trans hT.le
    rw [tendstoInMeasure_iff_norm]
    intro ε he
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hA T ε he)
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => measure_mono ?_)
    intro ω hw
    have hnot : ¬ ∀ j, ‖Y n ω (τ j)-X n ω (τ j)‖ < ε := by
      intro hh
      change ε ≤ ‖(L-K) n ω - (0 : Ω → Fin q → Fin k → ℝ) ω‖ at hw
      apply hw.not_gt
      apply (pi_norm_lt_iff he).2
      simpa only [Pi.sub_apply,Pi.zero_apply,sub_zero] using hh
    push Not at hnot
    obtain ⟨j,hj⟩ := hnot
    exact ⟨τ j,⟨hτ j,hbound j⟩,hj⟩
  · intro T ε η he hn
    obtain ⟨δ,hδ,hM⟩ := hM T (ε/3) (η/2) (by positivity) (by positivity)
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hM,(hA T (ε/3) (by positivity)).eventually_lt_const
      (ENNReal.ofReal_pos.2 (by positivity : 0 < η/2))] with n hm ha
    let SA := {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε/3 ≤ ‖Y n ω t-X n ω t‖}
    let SM := {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
      ε/3 ≤ ‖X n ω s-X n ω t‖}
    calc
      _ ≤ P (SA ∪ SM) := by
        apply measure_mono
        rintro ω ⟨s,hs,t,ht,hst,hb⟩
        by_contra hBad
        have hsa : ‖Y n ω s-X n ω s‖ < ε/3 := lt_of_not_ge
          (fun h => hBad (Or.inl ⟨s,hs,h⟩))
        have hta : ‖Y n ω t-X n ω t‖ < ε/3 := lt_of_not_ge
          (fun h => hBad (Or.inl ⟨t,ht,h⟩))
        have hst' : ‖X n ω s-X n ω t‖ < ε/3 := lt_of_not_ge
          (fun h => hBad (Or.inr ⟨s,hs,t,ht,hst,h⟩))
        have hu (s t : ℝ) :
            ‖Y n ω s-Y n ω t‖ ≤ ‖Y n ω s-X n ω s‖ +
              ‖X n ω s-X n ω t‖+‖Y n ω t-X n ω t‖ := by
          have h := (dist_triangle4 (Y n ω s) (X n ω s) (X n ω t) (Y n ω t))
          rw [dist_comm (X n ω t) (Y n ω t)] at h
          simpa only [dist_eq_norm,add_assoc] using h
        linarith [hu s t]
      _ ≤ P SA+P SM := measure_union_le _ _
      _ ≤ ENNReal.ofReal (η/2)+ENNReal.ofReal (η/2) := add_le_add ha.le hm
      _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
