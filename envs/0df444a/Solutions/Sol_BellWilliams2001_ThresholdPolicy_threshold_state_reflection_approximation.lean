-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_state_reflection_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:37.764525+00:00
-- url     : https://prove2.me/submissions/1bf60792-6a3d-415a-ba47-d0350b115ef2

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_workload_reflection
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

private theorem zero_count_partial_sum {f : ℕ → ℝ} (hf : ∀ i, 1 ≤ i → 0 < f i) :
    renewalCount (partialSum f) 0 = 0 := by
  apply le_antisymm _ bot_le
  refine iSup_le fun m => iSup_le fun hm => ?_
  have hz : m = 0 := by
    by_contra! h
    have he : m ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega,le_rfl⟩
    have hh : f m ≤ partialSum f m := Finset.single_le_sum
      (fun i hi => (hf i (Finset.mem_Icc.1 hi).1).le) he
    exact ((hf m (by omega)).trans_le hh).not_ge hm
  simp [hz]

private theorem queue_zero {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) (k : Fin 2) :
    M.queue n T ω k 0 = 0 := by
  have ha (j : Fin 2) : renewalCount (M.xi n j ω) 0 = 0 :=
    zero_count_partial_sum (fun i hi => div_pos (M.uC_pos j i ω hi) (M.lamR_pos n j))
  have hs (j : Fin 3) : renewalCount (M.eta n j ω) 0 = 0 :=
    zero_count_partial_sum (fun i hi => div_pos (M.vC_pos j i ω hi) (M.muR_pos n j))
  by_cases hk : k = 0 <;> simp [hk,SystemSequence.queue,SystemSequence.A,SystemSequence.S,hA.alloc_zero,ha,hs]


private theorem workload_input_bounded_below {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω)
    (t : ℝ) (ht : 0 ≤ t) :
    BddBelow (range (fun s : Icc (0:ℝ) t => M.workloadInput n T ω s)) := by
  let v (s : ℝ) := M.muR n 0 * M.Ihat n T ω s 0 + M.muR n 1 * M.Ihat n T ω s 1
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  refine ⟨-v t, fun _ ⟨s,hs⟩ => hs ▸ ?_⟩
  have hs0 : 0 ≤ M.r n^2 * s := mul_nonneg (sq_nonneg _) s.2.1
  have ht0 : 0 ≤ M.r n^2 * t := mul_nonneg (sq_nonneg _) ht
  have hst : M.r n^2 * s ≤ M.r n^2 * t := mul_le_mul_of_nonneg_left s.2.2 (sq_nonneg _)
  have hI (k : Fin 2) : M.Ihat n T ω s k ≤ M.Ihat n T ω t k :=
    div_le_div_of_nonneg_right (hT.idle_mono ω k hs0 ht0 hst) hr.le
  have hv : v s ≤ v t := add_le_add (mul_le_mul_of_nonneg_left (hI 0) (M.muR_pos n 0).le)
    (mul_le_mul_of_nonneg_left (hI 1) (M.muR_pos n 1).le)
  have hq (k : Fin 2) : 0 ≤ M.Qhat n T ω s k :=
    div_nonneg (hT.queue_nonneg ω k _ hs0) hr.le
  have hw : 0 ≤ M.workload n T ω s :=
    add_nonneg (hq 0) (mul_nonneg (div_nonneg (M.muR_pos n 1).le (M.muR_pos n 2).le) (hq 1))
  rw [workload_balance,SystemSequence.serverTwoInput] at hw
  dsimp only [v] at hv ⊢
  linarith

set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    let x := M.workloadInput n T ω
    let v := -(⨅ s : Icc (0:ℝ) t, x s)
    let e := (M.threshold c n:ℝ)/M.r n
    let i := M.Ihat n T ω t 0
    let q := M.Qhat n T ω t 0
    |M.Qhat n T ω t 1-(x t+v)/M.poolingWeight n| ≤
      (2*M.muR n 0*i + e + q)/M.poolingWeight n ∧
    |M.Ihat n T ω t 1-v/M.muR n 1| ≤ (M.muR n 0*i + e)/M.muR n 1 := by
  let x := M.workloadInput n T ω
  let v := -(⨅ s : Icc (0:ℝ) t, x s)
  let x' := M.serverTwoInput n T ω
  let v' := -(⨅ s : Icc (0:ℝ) t, x' s)
  let e := (M.threshold c n:ℝ)/M.r n
  let i := M.Ihat n T ω t 0
  let q := M.Qhat n T ω t 0
  let l := M.muR n 1 * M.Ihat n T ω t 1
  let d := M.muR n 0 * i
  have hR : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hY : 0 < M.poolingWeight n := div_pos (M.muR_pos n 1) (M.muR_pos n 2)
  have hI (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      0 ≤ M.Ihat n T ω s 0 ∧ M.Ihat n T ω s 0 ≤ i := by
    have hss : 0 ≤ M.r n^2*s := mul_nonneg (sq_nonneg _) hs
    have hst' : M.r n^2*s ≤ M.r n^2*t := mul_le_mul_of_nonneg_left hst (sq_nonneg _)
    have h0 := hA.idle_mono ω 0 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      hss hss
    rw [hA.idle_zero] at h0
    exact ⟨div_nonneg h0 hR.le,div_le_div_of_nonneg_right
      (hA.idle_mono ω 0 hss (hss.trans hst') hst') hR.le⟩
  have hD0 : 0 ≤ d := mul_nonneg (M.muR_pos n 0).le (hI t ht le_rfl).1
  have hE0 : 0 ≤ e := div_nonneg (Nat.cast_nonneg _) hR.le
  have hQ0 : 0 ≤ q := div_nonneg (hA.queue_nonneg ω 0 _ (mul_nonneg (sq_nonneg _) ht)) hR.le
  letI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,le_rfl,ht⟩⟩
  have hX := workload_input_bounded_below M n T hA ω t ht
  have hLe (s : Icc (0:ℝ) t) : x s ≤ x' s ∧ x' s ≤ x s+d := by
    have hz := hI s s.2.1 s.2.2
    exact ⟨le_add_of_nonneg_right (mul_nonneg (M.muR_pos n 0).le hz.1),
      add_le_add_right (mul_le_mul_of_nonneg_left hz.2 (M.muR_pos n 0).le) _⟩
  have hX' : BddBelow (range (fun s : Icc (0:ℝ) t => x' s)) := by
    obtain ⟨b,hb⟩ := hX
    exact ⟨b,fun _ ⟨s,hs⟩ => hs ▸ (hb ⟨s,rfl⟩).trans (hLe s).1⟩
  have hv₁ : v' ≤ v := neg_le_neg (le_ciInf fun s => (ciInf_le hX s).trans (hLe s).1)
  have hv₂ : v-d ≤ v' := by
    have h : (⨅ s : Icc (0:ℝ) t, x' s) - d ≤ ⨅ s : Icc (0:ℝ) t, x s := by
      refine le_ciInf fun s => ?_
      exact sub_le_iff_le_add.2 ((ciInf_le hX' s).trans (hLe s).2)
    dsimp only [v,v']
    linarith
  have hAt0 : M.serverTwoInput n T ω 0 = 0 := by
    have h := workload_balance M n T ω 0
    simpa [SystemSequence.workload,SystemSequence.Qhat,queue_zero M n T hA ω,
      SystemSequence.Ihat,hA.idle_zero] using h.symm
  obtain ⟨hLow,hUp⟩ := threshold_workload_reflection M c n T hA hP ω t ht hAt0 hX'
  change v' ≤ l at hLow
  change l ≤ v'+e at hUp
  have hDiff : |l-v| ≤ d+e := abs_le.2 ⟨by linarith,by linarith⟩
  have hBal : q + M.poolingWeight n * M.Qhat n T ω t 1 = x t+d+l := workload_balance M n T ω t
  have hQ : M.Qhat n T ω t 1-(x t+v)/M.poolingWeight n =
      (d+(l-v)-q)/M.poolingWeight n := by
    apply (eq_div_iff hY.ne').2
    field_simp [hY.ne']
    linarith
  constructor
  · rw [hQ,abs_div,abs_of_pos hY,show 2*M.muR n 0*i = 2*d by dsimp only [d]; ring]
    apply div_le_div_of_nonneg_right _ hY.le
    have h := (abs_sub (d+(l-v)) q).trans (add_le_add_left (abs_add_le d (l-v)) _)
    rw [abs_of_nonneg hD0,abs_of_nonneg hQ0] at h
    linarith
  · have heq : M.Ihat n T ω t 1-v/M.muR n 1 = (l-v)/M.muR n 1 := by
      dsimp only [l]
      field_simp [(M.muR_pos n 1).ne']
    rw [heq,abs_div,abs_of_pos (M.muR_pos n 1)]
    exact div_le_div_of_nonneg_right hDiff (M.muR_pos n 1).le
