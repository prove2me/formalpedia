-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.admissible_workload_and_idle_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:36.703238+00:00
-- url     : https://prove2.me/submissions/d7bd679c-89c2-42b2-acf9-27fb9c462cc5

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_queue_regularity
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

private theorem cadlag_add {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun t => f t+g t) := by
  refine ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht), fun t ht => ?_⟩
  obtain ⟨l,hl⟩ := hf.2 t ht
  obtain ⟨k,hk⟩ := hg.2 t ht
  exact ⟨l+k,hl.add hk⟩

private theorem cadlag_scale {f : ℝ → ℝ} (hf : IsCadlag f) (c : ℝ) :
    IsCadlag (fun t => c*f t) := by
  refine ⟨fun t ht => (hf.1 t ht).const_mul c, fun t ht => ?_⟩
  obtain ⟨l,hl⟩ := hf.2 t ht
  exact ⟨c*l,hl.const_mul c⟩

private theorem cadlag_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) :
    IsCadlag f := by
  refine ⟨fun t ht => (hf t ht).mono (fun _ hs => ht.trans hs),fun t ht => ?_⟩
  have ha : ContinuousAt f t := (hf t ht.le).continuousAt (mem_of_superset (Ioi_mem_nhds ht) Ioi_subset_Ici_self)
  exact ⟨f t,ha.continuousWithinAt.tendsto⟩

set_option maxHeartbeats 1400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) :
    (∀ ω k, IsCadlag (fun t => M.Ihat n T ω t k)) ∧
    (∀ t, 0 ≤ t → ∀ k, AEMeasurable (fun ω => M.Ihat n T ω t k) M.P) ∧
    (∀ ω, IsCadlag (M.workloadInput n T ω)) ∧
    (∀ t, 0 ≤ t → AEMeasurable (fun ω => M.workloadInput n T ω t) M.P) := by
  let R := M.r n^2
  have hR : 0 ≤ R := sq_nonneg _
  have hIc (ω : Ω) (k : Fin 2) : ContinuousOn (fun t => M.Ihat n T ω t k) (Ici 0) :=
    ((hA.idle_cont ω k).comp ((continuous_const.mul continuous_id).continuousOn)
      (fun _ hs => mul_nonneg hR hs)).div_const _
  have hIm (t : ℝ) (ht : 0 ≤ t) (k : Fin 2) :
      AEMeasurable (fun ω => M.Ihat n T ω t k) M.P := by
    have ht' : 0 ≤ R*t := mul_nonneg hR ht
    let u := R*t
    have hT (j : Fin 3) := hA.meas j u ht'
    by_cases hk : k = 0
    · simpa only [SystemSequence.Ihat, SystemSequence.idle, if_pos hk, Pi.sub_def] using
        ((hT 0).const_sub u).div_const (M.r n)
    · simpa only [SystemSequence.Ihat, SystemSequence.idle, if_neg hk, Pi.sub_def] using
        (((hT 1).const_sub u).sub (hT 2)).div_const (M.r n)
  let F (ω : Ω) (s : ℝ) := M.Qhat n T ω s 0 + M.poolingWeight n*M.Qhat n T ω s 1 +
    -(M.muR n 0)*M.Ihat n T ω s 0 + -(M.muR n 1)*M.Ihat n T ω s 1
  have hF (ω : Ω) (s : ℝ) : M.workloadInput n T ω s = F ω s := by
    have h := workload_balance M n T ω s
    dsimp only [F,SystemSequence.workload,SystemSequence.serverTwoInput] at h ⊢
    linarith
  obtain ⟨hq,hqm⟩ := admissible_queue_regularity M n T hA
  refine ⟨fun ω k => cadlag_of_continuousOn (hIc ω k), hIm, ?_,?_⟩
  · intro ω
    have he : M.workloadInput n T ω = F ω := funext (hF ω)
    rw [he]
    exact cadlag_add (cadlag_add (cadlag_add (hq ω 0)
      (cadlag_scale (hq ω 1) _)) (cadlag_scale (cadlag_of_continuousOn (hIc ω 0)) _))
      (cadlag_scale (cadlag_of_continuousOn (hIc ω 1)) _)
  · intro t ht
    simp_rw [hF]
    exact (((hqm t ht 0).add ((hqm t ht 1).const_mul _)).add
      ((hIm t ht 0).const_mul _)).add ((hIm t ht 1).const_mul _)
