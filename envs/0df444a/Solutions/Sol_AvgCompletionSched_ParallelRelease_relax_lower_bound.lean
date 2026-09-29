-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.relax_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:19:27.0129+00:00
-- url     : https://prove2.me/submissions/084a6604-11fe-42be-90c3-8a6622fea22c

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

namespace AvgCompletionSched.ParallelRelease

open MeasureTheory

/-- The number of jobs running at time `t` in a nonpreemptive schedule is at most `m`. -/
theorem aux_rlb_card {n m : ℕ} (I : Instance n m) (N : Schedule I) (t : ℝ) :
    (Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))).card ≤ m := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))) (t := (Finset.univ : Finset (Fin m)))
      N.M (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  · simpa using h
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Set.mem_Ico] at hi hj
    by_contra hne
    rcases N.noOverlap i j hij hne with h1 | h1
    · linarith [hi.1, hi.2, hj.1, hj.2]
    · linarith [hi.1, hi.2, hj.1, hj.2]

/-- The time-sliced relaxation schedule obtained from a nonpreemptive schedule: job `j` is
processed at rate `1/m` during `[S j, S j + p j)`. -/
noncomputable def aux_rlb_relax {n m : ℕ} (I : Instance n m) (N : Schedule I) :
    RelaxSchedule I where
  ρ j := (Set.Ico (N.S j) (N.S j + I.p j)).indicator (fun _ => (1 / (m : ℝ)))
  measurable j := (measurable_const).indicator measurableSet_Ico
  integrable j := by
    refine (integrable_indicator_iff measurableSet_Ico).2 ?_
    exact integrableOn_const (by simp [Real.volume_Ico])
  nonneg j t := by
    apply Set.indicator_nonneg
    intro _ _
    positivity
  capacity t := by
    have hm : (0 : ℝ) < m := by exact_mod_cast I.m_pos
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := aux_rlb_card I N t
    have hc' : ((Finset.univ.filter (fun j => t ∈ Set.Ico (N.S j) (N.S j + I.p j))).card : ℝ)
        ≤ m := by exact_mod_cast hc
    calc _ ≤ (m : ℝ) * (1 / (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hc'
          positivity
      _ = 1 := by field_simp
  released j t ht := by
    apply Set.indicator_of_notMem
    intro hmem
    have := N.released j
    have := hmem.1
    linarith
  total j := by
    rw [integral_indicator_const _ measurableSet_Ico,
      Real.volume_real_Ico_of_le (by linarith [I.p_pos j])]
    simp only [smul_eq_mul]
    ring
  bounded j := by
    refine ⟨N.S j + I.p j, fun t ht => ?_⟩
    apply Set.indicator_of_notMem
    intro hmem
    have := hmem.2
    linarith

theorem aux_rlb_CP_le {n m : ℕ} (I : Instance n m) (N : Schedule I) (j : Fin n) :
    (aux_rlb_relax I N).CP j ≤ N.C j := by
  unfold RelaxSchedule.CP
  by_cases hb : BddBelow {t | I.p j / m ≤ (aux_rlb_relax I N).done j t}
  · apply csInf_le hb
    show I.p j / m ≤ (aux_rlb_relax I N).done j (N.S j + I.p j)
    unfold RelaxSchedule.done
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [(aux_rlb_relax I N).total j]
    · intro x hx
      show (Set.Ico (N.S j) (N.S j + I.p j)).indicator (fun _ => (1 / (m : ℝ))) x = 0
      apply Set.indicator_of_notMem
      intro hmem
      exact hx hmem.2
  · rw [Real.sInf_of_not_bddBelow hb]
    unfold Schedule.C
    linarith [N.released j, I.r_nonneg j, I.p_pos j]

end AvgCompletionSched.ParallelRelease

open AvgCompletionSched.ParallelRelease

theorem solution {n m : ℕ} (I : Instance n m) (P1 : RelaxSchedule I)
    (hP1 : P1.IsOptimal) (Nstar : Schedule I) :
    ∑ j, P1.CP j ≤ ∑ j, Nstar.C j := by
  calc ∑ j, P1.CP j ≤ ∑ j, (aux_rlb_relax I Nstar).CP j := hP1 _
    _ ≤ ∑ j, Nstar.C j := Finset.sum_le_sum (fun j _ => aux_rlb_CP_le I Nstar j)
