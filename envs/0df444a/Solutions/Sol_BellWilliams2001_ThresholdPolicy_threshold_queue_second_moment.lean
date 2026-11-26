-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_queue_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:15.53636+00:00
-- url     : https://prove2.me/submissions/0db40a3b-85d8-4b98-86ab-16aef3a36807

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_idle_one_second_moment
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_diffusion_second_moment_majorants
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_workload_reflection
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

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


private theorem clock_range {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) (j : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.Tbar n T ω s j ∧ M.Tbar n T ω s j ≤ s := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have h0 : (0:ℝ) ∈ Ici (0:ℝ) := mem_Ici.mpr le_rfl
  have hu : R*s ∈ Ici (0:ℝ) := mul_nonneg hR.le hs
  have hNon (i : Fin 3) : 0 ≤ T ω i (R*s) := by
    have h := hA.alloc_mono ω i h0 hu hu
    rwa [hA.alloc_zero] at h
  refine ⟨div_nonneg (hNon j) hR.le, ?_⟩
  change T ω j (R*s) / R ≤ s
  rw [div_le_iff₀ hR, mul_comm s]
  have h0 := hA.idle_mono ω 0 h0 hu hu
  have h1 := hA.idle_mono ω 1 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hu hu
  rw [hA.idle_zero] at h0 h1
  simp only [SystemSequence.idle,if_true, show (1:Fin 2) ≠ 0 by decide,if_false] at h0 h1
  fin_cases j <;> simp at *
  · linarith
  · linarith [hNon 2]
  · linarith [hNon 1]

private theorem parameter_bounds {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (hc : 0 < c) : ∃ D : ℝ, 1 ≤ D ∧ ∀ n,
      M.h 0 ≤ D ∧ M.h 1 / M.poolingWeight n ≤ D ∧ M.poolingWeight n ≤ D ∧
      M.muR n 0 ≤ D ∧ |M.driftR n 0| ≤ D ∧ |M.driftR n 1| ≤ D ∧
      (M.threshold c n:ℝ) / M.r n ≤ D := by
  let y := M.mu 1 / M.mu 2
  let v (n : ℕ) := M.poolingWeight n
  have hy : 0 < y := div_pos (M.mu_pos 1) (M.mu_pos 2)
  have hv : Tendsto v atTop (𝓝 y) := (M.a31_iv 1).div (M.a31_iv 2) (M.mu_pos 2).ne'
  have h0 : Tendsto (fun n => M.driftR n 0) atTop (𝓝 (M.theta 0)) := M.a31_v
  have h1 : Tendsto (fun n => M.driftR n 1) atTop (𝓝 (M.theta 1)) := by
    simpa only [SystemSequence.driftR,show (1:Fin 2) ≠ 0 by decide,if_false] using M.a31_vi
  let b (n : ℕ) := M.h 0 + M.h 1 / v n + v n + M.muR n 0 + |M.driftR n 0| + |M.driftR n 1| + c
  have ht := ((((((tendsto_const_nhds (x := M.h 0)).add
    ((tendsto_const_nhds (x := M.h 1)).div hv hy.ne')).add hv).add (M.a31_iv 0)).add h0.abs).add h1.abs).add
    (tendsto_const_nhds (x := c))
  obtain ⟨a,ha⟩ := (Metric.isBounded_range_of_tendsto b ht).bddAbove
  let D := max a 1
  refine ⟨D,le_max_right _ _,fun n => ?_⟩
  have hB : b n ≤ D := (ha ⟨n,rfl⟩).trans (le_max_left _ _)
  have hV : 0 < v n := div_pos (M.muR_pos n 1) (M.muR_pos n 2)
  have hDiv : 0 ≤ M.h 1/v n := div_nonneg (M.h_pos 1).le hV.le
  have h0p := M.h_pos 0
  have hm := M.muR_pos n 0
  have hb (x : ℝ) : x ≤ b n → x ≤ D := fun h => h.trans hB
  refine ⟨hb (M.h 0) ?_,hb (M.h 1/v n) ?_,hb (v n) ?_,hb (M.muR n 0) ?_,
    hb |M.driftR n 0| ?_,hb |M.driftR n 1| ?_, ?_⟩
  all_goals try (dsimp only [b]; linarith [abs_nonneg (M.driftR n 0),abs_nonneg (M.driftR n 1)])
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hLog : Real.log (M.r n) ≤ M.r n := (Real.log_le_sub_one_of_pos hr).trans (by linarith)
  have hf : (M.threshold c n:ℝ) ≤ c*Real.log (M.r n) :=
    Nat.floor_le (mul_nonneg hc.le (Real.log_nonneg (M.r_ge n)))
  have hfc : (M.threshold c n:ℝ)/M.r n ≤ c := (div_le_iff₀ hr).2
    (hf.trans (mul_le_mul_of_nonneg_left hLog hc.le))
  exact hfc.trans (hb c (by dsimp only [b]; linarith [abs_nonneg (M.driftR n 0),abs_nonneg (M.driftR n 1)]))

private theorem holding_bound {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (c : ℝ) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (D W : ℝ) (hD : 1 ≤ D) (hW : 0 ≤ W)
    (hpar : M.h 0 ≤ D ∧ M.h 1 / M.poolingWeight n ≤ D ∧ M.poolingWeight n ≤ D ∧
      M.muR n 0 ≤ D ∧ |M.driftR n 0| ≤ D ∧ |M.driftR n 1| ≤ D ∧
      (M.threshold c n:ℝ)/M.r n ≤ D)
    (hPr : ∀ s, 0 ≤ s → s ≤ t → (∀ k, |M.Ahat n ω s k| ≤ W) ∧ (∀ j, |M.Shat n ω s j| ≤ W)) :
    ∑ k, M.h k*M.Qhat n T ω t k ≤
      (D*(2*(3+2*D)+2*D*(1+D)+D+1)+1)*(W+M.Ihat n T ω t 0+(1+t)) := by
  obtain ⟨hh0,hh1,hy,hm,hδ0,hδ1,hL⟩ := hpar
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hy0 : 0 < M.poolingWeight n := div_pos (M.muR_pos n 1) (M.muR_pos n 2)
  have hI (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.Ihat n T ω s 0 := by
    refine div_nonneg ?_ hr.le
    have hu : 0 ≤ M.r n^2*s := mul_nonneg (sq_nonneg _) hs
    have hh := hA.idle_mono ω 0 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      (show M.r n^2*s ∈ Ici 0 from hu) hu
    rwa [hA.idle_zero] at hh
  let G := (3+2*D)*W+D*(1+D)*t
  have hX (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : |M.workloadInput n T ω s| ≤ G := by
    let T' := M.Tbar n T ω s
    have hsrv (j : Fin 3) := (hPr (T' j) (clock_range M n T hA ω j s hs).1
      ((clock_range M n T hA ω j s hs).2.trans hst)).2 j
    have harr := (hPr s hs hst).1
    have hDr (k : Fin 2) (hk : |M.driftR n k| ≤ D) : |M.driftR n k*s| ≤ D*t := by
      rw [abs_mul,abs_of_nonneg hs]
      exact mul_le_mul hk hst hs hD0
    have h0 : |M.Xhat n T ω s 0| ≤ 3*W+D*t := by
      simp only [SystemSequence.Xhat,if_true]
      have h := (abs_add_le (M.Ahat n ω s 0 - M.Shat n ω (T' 0) 0 - M.Shat n ω (T' 1) 1)
        (M.driftR n 0*s)).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) (hDr 0 hδ0))
      linarith [harr 0,hsrv 0,hsrv 1]
    have h1 : |M.Xhat n T ω s 1| ≤ 2*W+D*t := by
      simp only [SystemSequence.Xhat,show (1:Fin 2) ≠ 0 by decide,if_false]
      have h := (abs_add_le (M.Ahat n ω s 1 - M.Shat n ω (T' 2) 2) (M.driftR n 1*s)).trans
        (add_le_add (abs_sub _ _) (hDr 1 hδ1))
      linarith [harr 1,hsrv 2]
    have hP := mul_le_mul hy h1 (abs_nonneg _) hD0
    have hsum := abs_add_le (M.Xhat n T ω s 0) (M.poolingWeight n * M.Xhat n T ω s 1)
    rw [abs_mul,abs_of_pos hy0] at hsum
    dsimp [G,SystemSequence.workloadInput]
    linarith only [h0,hP,hsum]
  have hAt0 : M.serverTwoInput n T ω 0 = 0 := by
    have h := workload_balance M n T ω 0
    simpa [SystemSequence.workload,SystemSequence.Qhat,queue_zero M n T hA ω,
      SystemSequence.Ihat,hA.idle_zero] using h.symm
  have hLow (s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : -G ≤ M.serverTwoInput n T ω s := by
    have h := (abs_le.1 (hX s hs hst)).1
    have hIdle := mul_nonneg (M.muR_pos n 0).le (hI s hs)
    dsimp [SystemSequence.serverTwoInput]
    linarith
  have hBdd : BddBelow (range (fun s : Icc (0:ℝ) t => M.serverTwoInput n T ω s)) :=
    ⟨-G,fun _ ⟨s,hs⟩ => hs ▸ hLow s s.2.1 s.2.2⟩
  haveI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,le_rfl,ht⟩⟩
  have hInf : -G ≤ ⨅ s : Icc (0:ℝ) t, M.serverTwoInput n T ω s :=
    le_ciInf fun s => hLow s s.2.1 s.2.2
  have hRef := (threshold_workload_reflection M c n T hA hP ω t ht hAt0 hBdd).2
  have hWork : M.workload n T ω t ≤ 2*G+D*M.Ihat n T ω t 0+D := by
    rw [workload_balance M n T ω t,SystemSequence.serverTwoInput]
    have hx := (abs_le.1 (hX t ht le_rfl)).2
    have hi := mul_le_mul_of_nonneg_right hm (hI t ht)
    linarith
  have hHold : ∑ k, M.h k*M.Qhat n T ω t k ≤ D*M.workload n T ω t := by
    have hq (k : Fin 2) : 0 ≤ M.Qhat n T ω t k := div_nonneg (hA.queue_nonneg ω k _
      (mul_nonneg (sq_nonneg _) ht)) hr.le
    rw [Fin.sum_univ_two,SystemSequence.workload,mul_add,←mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_right hh0 (hq 0))
      (mul_le_mul_of_nonneg_right ((div_le_iff₀ hy0).1 hh1) (hq 1))
  refine hHold.trans ((mul_le_mul_of_nonneg_left hWork hD0).trans ?_)
  dsimp [G]
  let I := M.Ihat n T ω t 0
  change D*(2*((3+2*D)*W+D*(1+D)*t)+D*I+D) ≤
    (D*(2*(3+2*D)+2*D*(1+D)+D+1)+1)*(W+I+(1+t))
  have hI0 : 0 ≤ I := hI t ht
  let K := D*(2*(3+2*D)+2*D*(1+D)+D+1)+1
  have h₁ : D*(2*(3+2*D)) ≤ K := by dsimp [K]; nlinarith [mul_nonneg hD0 (show 0 ≤ 2*D*(1+D)+D+1 by positivity)]
  have h₂ : D*D ≤ K := by dsimp [K]; nlinarith [mul_nonneg hD0 (show 0 ≤ 2*(3+2*D)+2*D*(1+D)+1 by positivity)]
  have h₃ : D*(2*D*(1+D)) ≤ K := by dsimp [K]; nlinarith [mul_nonneg hD0 (show 0 ≤ 2*(3+2*D)+D+1 by positivity)]
  have h₄ : D*D ≤ K := h₂
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_right h₁ hW)
    (mul_le_mul_of_nonneg_right h₂ hI0)) (add_le_add (mul_le_mul_of_nonneg_right h₃ ht) h₄)
  linarith only [h]

set_option maxHeartbeats 2000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
        (∫⁻ ω, (ENNReal.ofReal (∑ k, M.h k * M.Qhat n (Tstar n) ω t k)) ^ 2 ∂M.P) ≤
          ENNReal.ofReal (C * (1 + t) ^ p) := by
  obtain ⟨c₀,hc₀,hId⟩ := threshold_idle_one_second_moment M
  refine ⟨c₀,hc₀,fun c hc T hT => ?_⟩
  have hc0 := hc₀.trans hc
  obtain ⟨D,hD,hpar⟩ := parameter_bounds M c hc0
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  obtain ⟨A,hA,hMomI⟩ := hId c hc T hT
  obtain ⟨B,hB,hPrim⟩ := primitive_diffusion_second_moment_majorants M
  let F := D*(2*(3+2*D)+2*D*(1+D)+D+1)+1
  have hF : 0 < F := by dsimp [F]; positivity
  let K := 3*F^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*(5*B+A+1),by positivity,3,?_⟩
  letI : IsProbabilityMeasure M.P := M.isProb
  have hElig : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop hc0
    exact (h.eventually_ge_atTop (1:ℝ)).mono (fun _ hn => (Nat.one_le_floor_iff _).mpr hn)
  filter_upwards [hMomI,hElig] with n hn hLn t ht
  obtain ⟨hAdm,hPolicy⟩ := hT n hLn
  obtain ⟨JA,JS,ha,hs,hAS⟩ := hPrim n t ht
  let Z (ω : Ω) := (∑ k, JA k ω) + ∑ j, JS j ω
  let I (ω : Ω) := M.Ihat n (T n) ω t 0
  let V := ENNReal.ofReal ((1+t)^2)
  let H (ω : Ω) := ∑ k, M.h k*M.Qhat n (T n) ω t k
  have hZmeas : Measurable Z := by
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun k _ => (ha k).1)
    · exact Finset.measurable_sum _ (fun j _ => (hs j).1)
  have hBound (ω : Ω) : ENNReal.ofReal (H ω)^2 ≤
      ENNReal.ofReal K*(Z ω+ENNReal.ofReal (I ω)^2+V) := by
    by_cases hZ : Z ω = ⊤
    · simp [hZ,ENNReal.ofReal_ne_zero_iff.mpr hK]
    let W := Real.sqrt (Z ω).toReal
    have hW : 0 ≤ W := Real.sqrt_nonneg _
    have hW2 : W^2 = (Z ω).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    have hWreal : ENNReal.ofReal (W^2) = Z ω := by rw [hW2,ENNReal.ofReal_toReal hZ]
    have hLe (x : ℝ) (hx : (ENNReal.ofReal |x|)^2 ≤ Z ω) : |x| ≤ W := by
      rw [← ENNReal.ofReal_pow (abs_nonneg x) 2] at hx
      exact Real.le_sqrt_of_sq_le ((ENNReal.ofReal_le_iff_le_toReal hZ).1 hx)
    have hPr (u : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) :
        (∀ k, |M.Ahat n ω u k| ≤ W) ∧ (∀ j, |M.Shat n ω u j| ≤ W) := by
      constructor
      · intro k
        exact hLe _ (((hAS ω u hu hut).1 k).trans
          ((Finset.single_le_sum (f := fun i => JA i ω) (fun _ _ => bot_le) (Finset.mem_univ k)).trans le_self_add))
      · intro j
        exact hLe _ (((hAS ω u hu hut).2 j).trans
          ((Finset.single_le_sum (f := fun i => JS i ω) (fun _ _ => bot_le) (Finset.mem_univ j)).trans (le_add_left le_rfl)))
    have hHR := holding_bound M n (T n) c hAdm hPolicy ω t ht D W hD hW (hpar n) hPr
    have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
    have hI0 : 0 ≤ I ω := by
      refine div_nonneg ?_ hr.le
      have hu : 0 ≤ M.r n^2*t := mul_nonneg (sq_nonneg _) ht
      have hi := hAdm.idle_mono ω 0 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
        (show M.r n^2*t ∈ Ici 0 from hu) hu
      rwa [hAdm.idle_zero] at hi
    have hH0 : 0 ≤ H ω := by
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (M.h_pos k).le (div_nonneg
        (hAdm.queue_nonneg ω k _ (mul_nonneg (sq_nonneg _) ht)) hr.le)
    have hSq : (H ω)^2 ≤ K*(W^2+(I ω)^2+(1+t)^2) := by
      have hHS : H ω^2 ≤ (F*(W+I ω+(1+t)))^2 := pow_le_pow_left₀ hH0 hHR 2
      have h3 : (W+I ω+(1+t))^2 ≤ 3*(W^2+(I ω)^2+(1+t)^2) := by
        nlinarith [sq_nonneg (W-I ω),sq_nonneg (W-(1+t)),sq_nonneg (I ω-(1+t))]
      rw [mul_pow] at hHS
      refine hHS.trans ((mul_le_mul_of_nonneg_left h3 (sq_nonneg F)).trans_eq ?_)
      dsimp [K]
      ring
    have h := ENNReal.ofReal_le_ofReal hSq
    rw [ENNReal.ofReal_pow hH0 2,ENNReal.ofReal_mul hK.le,
      ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (sq_nonneg W) (sq_nonneg _),
      hWreal, ENNReal.ofReal_pow hI0 2] at h
    exact h
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal K*(Z ω+ENNReal.ofReal (I ω)^2+V) ∂M.P := lintegral_mono hBound
    _ = ENNReal.ofReal K*((∫⁻ ω, Z ω ∂M.P) + (∫⁻ ω, ENNReal.ofReal (I ω)^2 ∂M.P) + V) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ measurable_const,
        lintegral_add_left hZmeas,lintegral_const,measure_univ,mul_one]
    _ ≤ _ := by
      have hZ : (∫⁻ ω, Z ω ∂M.P) ≤ ENNReal.ofReal (5*B*(1+t)) := by
        simp only [Z,Fin.sum_univ_two,Fin.sum_univ_three]
        have hma : Measurable (fun ω => JA 0 ω + JA 1 ω) := (ha 0).1.add (ha 1).1
        have hms : Measurable (fun ω => JS 0 ω + JS 1 ω) := (hs 0).1.add (hs 1).1
        rw [lintegral_add_left hma,lintegral_add_left (ha 0).1,
          lintegral_add_left hms,lintegral_add_left (hs 0).1]
        refine (add_le_add (add_le_add (ha 0).2 (ha 1).2)
          (add_le_add (add_le_add (hs 0).2 (hs 1).2) (hs 2).2)).trans_eq ?_
        repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      refine (mul_le_mul_right (add_le_add (add_le_add hZ (hn t ht)) le_rfl) _).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul hK.le]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc K]
      apply mul_le_mul_of_nonneg_left _ hK.le
      have h1 : 1 ≤ 1+t := by linarith
      have h2 : 1+t ≤ (1+t)^3 := by
        have h := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) h1) (show 0 ≤ 1+t by positivity)
        nlinarith
      have h3 : (1+t)^2 ≤ (1+t)^3 := by
        have h := mul_le_mul_of_nonneg_left h1 (sq_nonneg (1+t))
        nlinarith
      have hh := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 5*B by positivity)
      nlinarith
