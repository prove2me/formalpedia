-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_disjoint_iid_mark_sums_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:39:08.597401+00:00
-- url     : https://prove2.me/submissions/0a223439-0fa3-49c8-8ef1-c9baebdd90a8

import Mathlib.Probability.IdentDistrib
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_blocks_charfun_factor_20261111
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Finset
open scoped NNReal ENNReal
noncomputable section

/-- Transfer finite-dimensional characteristic factorisation to independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hNmono : ∀ ω, Monotone (fun i => N i ω))
    (hCount : iIndepFun (fun (i : Fin n) ω =>
      N i.succ ω - N i.castSucc ω) P)
    (hMarks : iIndepFun Y P)
    (hSameLaw : ∀ j k, IdentDistrib (Y j) (Y k) P P)
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P) :
    iIndepFun (fun (i : Fin n) ω =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P := by
  classical
  have hNcoord (i : Fin (n + 1)) : Measurable (N i) :=
    measurable_pi_iff.mp hN i
  have hPrefix (i : Fin (n + 1)) : Measurable
      (fun ω => ∑ j ∈ Finset.range (N i ω), Y j ω) := by
    have hRaw :=
      AvramDividend.Classical.variable_finite_marks_sum_measurable_ws01b
        (fun z : ℝ => z) measurable_id
    exact hRaw.comp ((hNcoord i).prodMk hY)
  have hBlockMeas (i : Fin n) : AEMeasurable
      (fun ω => ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω),
        Y j ω) P := by
    have heq : (fun ω => ∑ j ∈ Finset.Ico
        (N i.castSucc ω) (N i.succ ω), Y j ω) =
        (fun ω => (∑ j ∈ Finset.range (N i.succ ω), Y j ω) -
          (∑ j ∈ Finset.range (N i.castSucc ω), Y j ω)) := by
      funext ω
      exact Finset.sum_Ico_eq_sub (fun j => Y j ω)
        (hNmono ω (Fin.castSucc_le_succ i))
    rw [heq]
    exact ((hPrefix i.succ).sub (hPrefix i.castSucc)).aemeasurable
  apply (ProbabilityTheory.iIndepFun_iff_charFun_pi hBlockMeas).2
  exact AvramDividend.Classical.avram_a06_random_blocks_charfun_factor_20261111
    P n N Y hN hY hNmono hCount hMarks hSameLaw hSeparate
