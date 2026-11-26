-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_workload_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:59.861837+00:00
-- url     : https://prove2.me/submissions/b7d065cd-420f-4236-9f58-1bf248e35071

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_approximate_reflection
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Set
open scoped ENNReal

private theorem occupation_add {C : Set ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume (Ioc 0 b ∩ C)).toReal =
      (volume (Ioc 0 a ∩ C)).toReal + (volume (Ioc a b ∩ C)).toReal := by
  have h₁ : ((Ioc 0 b ∩ C) ∩ Ioc a b) = Ioc a b ∩ C := by
    ext s
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨_,hc⟩,hs⟩
      exact ⟨hs,hc⟩
    · rintro ⟨hs,hc⟩
      exact ⟨⟨⟨ha.trans_lt hs.1,hs.2⟩,hc⟩,hs⟩
  have h₂ : ((Ioc 0 b ∩ C) \ Ioc a b) = Ioc 0 a ∩ C := by
    ext s
    simp only [mem_sdiff, mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hs,hb⟩,hc⟩,h⟩
      exact ⟨⟨hs,le_of_not_gt fun hsa => h ⟨hsa,hb⟩⟩,hc⟩
    · rintro ⟨⟨hs,hsa⟩,hc⟩
      exact ⟨⟨⟨hs,hsa.trans hab⟩,hc⟩,fun h => (not_lt_of_ge hsa) h.1⟩
  have hf (u v : ℝ) : volume (Ioc u v ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top (Real.volume_Ioc ▸ ENNReal.ofReal_ne_top) (measure_mono inter_subset_left)
  have h := measure_sdiff_add_inter (μ := volume) (Ioc 0 b ∩ C) (measurableSet_Ioc (a := a) (b := b))
  rw [h₁,h₂] at h
  rw [← h, ENNReal.toReal_add (hf 0 a) (hf a b)]

private theorem idle_two_flat {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ∀ s ∈ Ioc a b, (M.threshold c n : ℝ) < M.queue n T ω 0 s ∨
      0 < M.queue n T ω 1 s) :
    SystemSequence.idle T ω 1 b = SystemSequence.idle T ω 1 a := by
  let C : Set ℝ := {s | (M.threshold c n : ℝ) < M.queue n T ω 0 s}
  let D : Set ℝ := {s | M.queue n T ω 0 s ≤ (M.threshold c n : ℝ) ∧ 0 < M.queue n T ω 1 s}
  have hCover : (Ioc a b ∩ C) ∪ (Ioc a b ∩ D) = Ioc a b := by
    ext s
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hs
      by_cases h : s ∈ C
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr ⟨hs,le_of_not_gt h,(hb s hs).resolve_left h⟩
  have hVol := measure_union_le (μ := volume) (Ioc a b ∩ C) (Ioc a b ∩ D)
  rw [hCover] at hVol
  have hf (E : Set ℝ) : volume (Ioc a b ∩ E) ≠ ⊤ :=
    ne_top_of_le_ne_top (Real.volume_Ioc ▸ ENNReal.ofReal_ne_top) (measure_mono inter_subset_left)
  have hOcc := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf C,hf D⟩) hVol
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ENNReal.toReal_add (hf C) (hf D)] at hOcc
  have hA1 : T ω 1 a = (volume (Ioc 0 a ∩ C)).toReal := (hP ω a ha).2.1
  have hB1 : T ω 1 b = (volume (Ioc 0 b ∩ C)).toReal := (hP ω b (ha.trans hab)).2.1
  have hA2 : T ω 2 a = (volume (Ioc 0 a ∩ D)).toReal := (hP ω a ha).2.2
  have hB2 : T ω 2 b = (volume (Ioc 0 b ∩ D)).toReal := (hP ω b (ha.trans hab)).2.2
  rw [occupation_add ha hab, ← hA1] at hB1
  rw [occupation_add ha hab, ← hA2] at hB2
  have hmon := hA.idle_mono ω 1 (show a ∈ Ici (0:ℝ) from ha)
    (show b ∈ Ici (0:ℝ) from ha.trans hab) hab
  simp only [SystemSequence.idle, show (1:Fin 2) ≠ 0 by decide, if_false] at hmon ⊢
  linarith

set_option maxHeartbeats 850000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (hZero : M.serverTwoInput n T ω 0 = 0)
    (hBound : BddBelow (Set.range (fun s : Set.Icc (0 : ℝ) t => M.serverTwoInput n T ω s))) :
    let v := -(⨅ s : Set.Icc (0 : ℝ) t, M.serverTwoInput n T ω s)
    v ≤ M.muR n 1 * M.Ihat n T ω t 1 ∧
      M.muR n 1 * M.Ihat n T ω t 1 ≤ v + (M.threshold c n : ℝ) / M.r n := by
  let R := M.r n ^ 2
  let x := M.serverTwoInput n T ω
  let l (s : ℝ) := M.muR n 1 * M.Ihat n T ω s 1
  let δ := (M.threshold c n : ℝ) / M.r n
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hR : 0 < R := pow_pos hr _
  have h0 : l 0 = 0 := by simp [l, SystemSequence.Ihat,hA.idle_zero]
  have hc : ContinuousOn l (Icc 0 t) := by
    apply ContinuousOn.const_mul
    change ContinuousOn (fun s => SystemSequence.idle T ω 1 (R*s) / M.r n) (Icc 0 t)
    apply ContinuousOn.div_const
    exact (hA.idle_cont ω 1).comp ((continuous_const.mul continuous_id).continuousOn)
      (fun s hs => mul_nonneg hR.le hs.1)
  have hmono : MonotoneOn l (Icc 0 t) := by
    intro a ha b hb hab
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (hA.idle_mono ω 1 (show R*a ∈ Ici (0:ℝ) from mul_nonneg hR.le ha.1)
          (show R*b ∈ Ici (0:ℝ) from mul_nonneg hR.le hb.1)
          (mul_le_mul_of_nonneg_left hab hR.le)) hr.le) (M.muR_pos n 1).le
  have hEq (s : ℝ) : x s + l s = M.workload n T ω s := (workload_balance M n T ω s).symm
  have hPos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ x s + l s := by
    rw [hEq]
    apply add_nonneg
    · exact div_nonneg (hA.queue_nonneg ω 0 _ (mul_nonneg hR.le hs)) hr.le
    · exact mul_nonneg (div_nonneg (M.muR_pos n 1).le (M.muR_pos n 2).le)
        (div_nonneg (hA.queue_nonneg ω 1 _ (mul_nonneg hR.le hs)) hr.le)
  apply approximate_reflection x l t ht δ (by dsimp [δ]; positivity) hZero hBound h0 hc hmono
    (fun s hs => hPos s hs.1)
  intro a b ha hab _ hGrow
  have hRaw : ∀ u ∈ Ioc (R*a) (R*b),
      (M.threshold c n : ℝ) < M.queue n T ω 0 u ∨ 0 < M.queue n T ω 1 u := by
    intro u hu
    let s := u / R
    have hes : R*s = u := mul_div_cancel₀ _ hR.ne'
    have hs : s ∈ Ioc a b := ⟨(lt_div_iff₀ hR).2 (by simpa [mul_comm a R] using hu.1),
      (div_le_iff₀ hR).2 (by simpa [mul_comm b R] using hu.2)⟩
    have hg := hGrow s hs
    rw [hEq] at hg
    change (M.threshold c n : ℝ) / M.r n < M.queue n T ω 0 (R*s) / M.r n +
      M.poolingWeight n * (M.queue n T ω 1 (R*s) / M.r n) at hg
    rw [hes, ← mul_div_assoc, ← add_div, div_lt_div_iff_of_pos_right hr] at hg
    by_cases hq : (M.threshold c n : ℝ) < M.queue n T ω 0 u
    · exact Or.inl hq
    · right
      have hProd : 0 < M.poolingWeight n * M.queue n T ω 1 u := by linarith
      exact pos_of_mul_pos_right hProd (div_nonneg (M.muR_pos n 1).le (M.muR_pos n 2).le)
  have hf := idle_two_flat M c n T hA hP ω (mul_nonneg hR.le ha)
    (mul_le_mul_of_nonneg_left hab hR.le) hRaw
  exact congrArg (fun z : ℝ => M.muR n 1 * (z / M.r n)) hf
