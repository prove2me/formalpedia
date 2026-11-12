-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_grid_marginal_charfun_mix_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:31:49.961656+00:00
-- url     : https://prove2.me/submissions/530a1873-b815-43e0-bf29-7797022a029b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_single_interval_charfun_disintegration_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_fourier_interval_charfun_power_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
noncomputable section

/-- Combine single-interval disintegration with the fixed-length mark-power identity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 2 ≤ n)
    (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (hFixed : ∀ (m : Fin (n + 1) → ℕ), Monotone m →
      ∀ t : WithLp 2 (Fin n → ℝ),
        MeasureTheory.charFun
          (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
          ∏ i : Fin n, MeasureTheory.charFun
            (Measure.map (fun ω : Ω =>
              ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
              (t.ofLp i)) :
    ∀ (t : WithLp 2 (Fin n → ℝ)) (i : Fin n),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) =
      ∫ ω, (MeasureTheory.charFun
        (Measure.map (Y 0) P) (t.ofLp i)) ^
          (N i.succ ω - N i.castSucc ω) ∂P := by
  intro t i
  rw [AvramDividend.Classical.avram_a06_single_interval_charfun_disintegration_20261111
    P n N Y hN hY hSeparate i (t.ofLp i)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hle : N i.castSucc ω ≤ N i.succ ω :=
    hNmono ω (Fin.castSucc_le_succ i)
  have hp := AvramDividend.Classical.avram_a06_fixed_fourier_interval_charfun_power_20261111
    P n hn Y (fun j => (measurable_pi_iff.mp hY) j)
    hSameLaw hFixed
    (N i.castSucc ω) (N i.succ ω - N i.castSucc ω) (t.ofLp i)
  simpa only [Nat.add_sub_of_le hle] using hp
