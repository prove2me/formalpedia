-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_blocks_charfun_factor_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:48:29.388516+00:00
-- url     : https://prove2.me/submissions/464bb518-3083-4780-b41a-a3b00858381f

import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_disjoint_mark_block_sums_independent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

/-- Fourier factorisation for disjoint, deterministic mark blocks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (hIndep : iIndepFun Y P) :
    ∀ t : WithLp 2 (Fin n → ℝ),
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
          ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω)) P) t =
        ∏ i : Fin n, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P)
          (t.ofLp i) := by
  have hInd :=
    AvramDividend.Classical.avram_a06_fixed_disjoint_mark_block_sums_independent
      P n m hm Y hY hIndep
  have hMeas : ∀ i : Fin n, AEMeasurable (fun ω =>
      ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) P := by
    intro i
    have h : Measurable (fun ω =>
        ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), Y j ω) := by
      fun_prop
    exact h.aemeasurable
  exact (ProbabilityTheory.iIndepFun_iff_charFun_pi hMeas).mp hInd
