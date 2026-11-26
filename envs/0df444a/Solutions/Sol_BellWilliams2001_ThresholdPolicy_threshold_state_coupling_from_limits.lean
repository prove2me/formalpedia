-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_state_coupling_from_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:09:25.651852+00:00
-- url     : https://prove2.me/submissions/f59c85c7-f3b8-4ff3-a03c-a51fb405d2c8

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_input_coupling_after_fluid_allocation
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_state_reflection_approximation
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_reflected_finite_observations_from_coupling
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_reflected_process_modulus
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_coupling_from_ae_process_limits
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_approximate_process_limits
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_workload_and_idle_regularity

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

private theorem past_infimum_modulus (x : ℝ → ℝ) {s t e : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (he : 0 ≤ e) (hBs : BddBelow (range (fun u : Icc (0:ℝ) s => x u)))
    (hBt : BddBelow (range (fun u : Icc (0:ℝ) t => x u)))
    (h : ∀ u ∈ Icc s t, |x u-x s| ≤ e) :
    |(⨅ u : Icc (0:ℝ) s, x u)-(⨅ u : Icc (0:ℝ) t, x u)| ≤ e := by
  letI : Nonempty (Icc (0:ℝ) s) := ⟨⟨0,le_rfl,hs⟩⟩
  letI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,le_rfl,hs.trans hst⟩⟩
  let I := ⨅ u : Icc (0:ℝ) s, x u
  let J := ⨅ u : Icc (0:ℝ) t, x u
  have h1 : J ≤ I :=
    le_ciInf fun u : Icc (0:ℝ) s => ciInf_le hBt ⟨u,u.2.1,u.2.2.trans hst⟩
  have h2 : I-e ≤ J := by
    apply le_ciInf
    intro u
    by_cases hu : (u:ℝ) ≤ s
    · exact (sub_le_self _ he).trans (ciInf_le hBs ⟨u,u.2.1,hu⟩)
    · have hh := (abs_le.1 (h u ⟨(lt_of_not_ge hu).le,u.2.2⟩)).1
      have hI : I ≤ x s := ciInf_le hBs ⟨s,hs,le_rfl⟩
      linarith
  change |I-J| ≤ e
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith

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

private theorem continuous_past_infimum (x : ℝ → ℝ) (hx : Continuous x) :
    ContinuousOn (fun t => ⨅ s : Icc (0:ℝ) t, x s) (Ici (0:ℝ)) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.2
  intro ε he
  have hT : UniformContinuousOn x (Icc 0 (t+1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hx.continuousOn
  obtain ⟨δ,hδ,hw⟩ := Metric.uniformContinuousOn_iff.1 hT (ε/2) (by positivity)
  refine ⟨min 1 δ,lt_min zero_lt_one hδ,?_⟩
  intro v hv hvt
  have hvt' : |v-t| < min 1 δ := by simpa only [Real.dist_eq] using hvt
  have hvT : v ≤ t+1 := by linarith [(abs_lt.1 (hvt'.trans_le (min_le_left _ _))).2]
  have hb (u : ℝ) : BddBelow (range (fun s : Icc (0:ℝ) u => x s)) := by
    rw [←Set.image_eq_range]
    exact (isCompact_Icc.image hx).bddBelow
  have hr (u w : ℝ) (hu : 0 ≤ u) (huw : u ≤ w) (hwT : w ≤ t+1) (hNear : |w-u| < δ) :
      |(⨅ s : Icc (0:ℝ) u,x s)-(⨅ s : Icc (0:ℝ) w,x s)| ≤ ε/2 := by
    refine past_infimum_modulus x hu huw (by positivity) (hb u) (hb w) ?_
    intro s hs
    have hh : |s-u| < δ := by
      rw [abs_of_nonneg (sub_nonneg.2 hs.1)]
      rw [abs_of_nonneg (sub_nonneg.2 huw)] at hNear
      linarith [hs.2]
    have h := hw s ⟨hu.trans hs.1,hs.2.trans hwT⟩ u ⟨hu,huw.trans hwT⟩ (by simpa [Real.dist_eq] using hh)
    simpa only [Real.dist_eq] using h.le
  rw [Real.dist_eq]
  rcases le_total v t with h | h
  · exact (hr v t hv h (by linarith) (by rw [abs_sub_comm]; exact hvt'.trans_le (min_le_right _ _))).trans_lt
      (by linarith)
  · rw [abs_sub_comm]
    exact (hr t v ht h hvT (hvt'.trans_le (min_le_right _ _))).trans_lt (by linarith)

set_option maxHeartbeats 4600000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (hc : 0 < c) (T : ℕ → Allocation Ω)
    (hT : ∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n))
    (hResidual : UocInProb M.P
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Ihat n (T n) ω t 0]) (fun _ => 0))
    (hFluid : UocInProb M.P (fun n ω t => M.Tbar n (T n) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    CouplingConverges M.P P'
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Qhat n (T n) ω t 1,
        M.Ihat n (T n) ω t 0, M.Ihat n (T n) ω t 1])
      (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]) := by
  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  letI : IsProbabilityMeasure P' := hB.isProb
  have hElig : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop hc
    exact (h.eventually_ge_atTop (1:ℝ)).mono (fun _ hn => (Nat.one_le_floor_iff _).mpr hn)
  let G (n : ℕ) := 1 ≤ M.threshold c n
  let x (n : ℕ) (ω : Ω) (t : ℝ) := if G n then M.workloadInput n (T n) ω t else 0
  let z (ω : Ω') (t : ℝ) := ∑ i, M.yvec i*M.Xtilde B ω t i
  let a (n : ℕ) := (M.poolingWeight n)⁻¹
  let b (n : ℕ) := (M.muR n 1)⁻¹
  let A := (M.yvec 1)⁻¹
  let D := (M.mu 1)⁻¹
  let V (f : ℝ → ℝ) (t : ℝ) := -(⨅ s : Icc (0:ℝ) t, f s)
  let R (f : ℝ → ℝ) (t : ℝ) := f t+V f t
  let X (n : ℕ) (ω : Ω) (t : ℝ) := ![0,a n*R (x n ω) t,0,b n*V (x n ω) t]
  let Y (n : ℕ) (ω : Ω) (t : ℝ) : Fin 4 → ℝ := if G n then
    ![M.Qhat n (T n) ω t 0,M.Qhat n (T n) ω t 1,M.Ihat n (T n) ω t 0,M.Ihat n (T n) ω t 1] else 0
  let W (ω : Ω') (t : ℝ) := ![0,A*R (z ω) t,0,D*V (z ω) t]
  have hw : Tendsto (fun n => M.poolingWeight n) atTop (𝓝 (M.yvec 1)) := by
    simpa only [SystemSequence.poolingWeight,SystemSequence.yvec,show (1:Fin 2) ≠ 0 by decide,if_false,Pi.div_def]
      using (M.a31_iv 1).div (M.a31_iv 2) (M.mu_pos 2).ne'
  have hy : 0 < M.yvec 1 := div_pos (M.mu_pos 1) (M.mu_pos 2)
  have ha : Tendsto a atTop (𝓝 A) := hw.inv₀ hy.ne'
  have hb : Tendsto b atTop (𝓝 D) := (M.a31_iv 1).inv₀ (M.mu_pos 1).ne'
  have hZ : ∀ᵐ ω ∂P', Continuous (z ω) := by
    filter_upwards [ae_all_iff.2 (fun i => (hB.brownian i).cont)] with ω hω
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul ((hω j).comp continuous_real_toNNReal)))
  have hWc : ∀ᵐ ω ∂P', ContinuousOn (W ω) (Ici 0) := by
    filter_upwards [hZ] with ω hω
    have hV : ContinuousOn (V (z ω)) (Ici 0) := (continuous_past_infimum _ hω).neg
    have hR : ContinuousOn (R (z ω)) (Ici 0) := hω.continuousOn.add hV
    apply continuousOn_pi.2
    intro i
    fin_cases i
    · exact continuousOn_const
    · exact hR.const_mul A
    · exact continuousOn_const
    · exact hV.const_mul D
  have hXc (n : ℕ) (ω : Ω) : IsCadlag (x n ω) := by
    by_cases hn : G n
    · simpa only [x,if_pos hn] using (admissible_workload_and_idle_regularity M n (T n) (hT n hn).1).2.2.1 ω
    · simpa only [x,if_neg hn] using (show IsCadlag (fun _ => (0:ℝ)) from
        ⟨fun _ _ => continuousWithinAt_const,fun _ _ => ⟨0,tendsto_const_nhds⟩⟩)
  have hXm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => x n ω t) M.P := by
    by_cases hn : G n
    · simpa only [x,if_pos hn] using (admissible_workload_and_idle_regularity M n (T n) (hT n hn).1).2.2.2 t ht
    · simpa only [x,if_neg hn] using aemeasurable_const
  have hYm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : AEMeasurable (fun ω => Y n ω t) M.P := by
    by_cases hn : G n
    · have hq := (admissible_queue_regularity M n (T n) (hT n hn).1).2 t ht
      have hi := (admissible_workload_and_idle_regularity M n (T n) (hT n hn).1).2.1 t ht
      apply aemeasurable_pi_lambda
      intro j
      fin_cases j
      · simpa [Y,hn] using hq 0
      · simpa [Y,hn] using hq 1
      · simpa [Y,hn] using hi 0
      · simpa [Y,hn] using hi 1
    · simpa only [Y,if_neg hn] using aemeasurable_const
  have hYc (n : ℕ) (ω : Ω) (i : Fin 4) : IsCadlag (fun t => Y n ω t i) := by
    by_cases hn : G n
    · have hq := (admissible_queue_regularity M n (T n) (hT n hn).1).1 ω
      have hi := (admissible_workload_and_idle_regularity M n (T n) (hT n hn).1).1 ω
      fin_cases i
      · simpa [Y,hn] using hq 0
      · simpa [Y,hn] using hq 1
      · simpa [Y,hn] using hi 0
      · simpa [Y,hn] using hi 1
    · simpa only [Y,if_neg hn,Pi.zero_apply] using (show IsCadlag (fun _ => (0:ℝ)) from
        ⟨fun _ _ => continuousWithinAt_const,fun _ _ => ⟨0,tendsto_const_nhds⟩⟩)
  obtain ⟨hU,hM⟩ := workload_input_coupling_after_fluid_allocation M id tendsto_id T
    (hElig.mono fun n hn => (hT n hn).1) hFluid Ω' P' B hB
  have hCouple : CouplingConverges M.P P' (fun n ω t => ![x n ω t]) (fun ω t => ![z ω t]) := by
    obtain ⟨Λ,mΛ,Q,U,F,hQ,hLaw,hLimit,hCad,hConv⟩ := hU
    refine ⟨Λ,mΛ,Q,U,F,hQ,?_,hLimit,hCad,hConv⟩
    filter_upwards [hElig,hLaw] with n hn hl
    simpa only [x,if_pos (show G n from hn),id_eq] using hl
  have hMod (H : ℕ) (ε η : ℝ) (he : 0 < ε) (hn : 0 < η) : ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (H:ℝ), ∃ t ∈ Icc (0:ℝ) (H:ℝ), |s-t| ≤ δ ∧
        ε ≤ |x n ω s-x n ω t|} ≤ ENNReal.ofReal η := by
    obtain ⟨δ,hδ,h⟩ := hM H ε η he hn
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hElig,h] with n hn hh
    simpa only [x,if_pos (show G n from hn),id_eq] using hh
  have hBdd : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t → BddBelow (range (fun s : Icc (0:ℝ) t => x n ω s)) := by
    filter_upwards [hElig] with n hn ω t ht
    simpa only [x,if_pos (show G n from hn)] using workload_input_bounded_below M n (T n) (hT n hn).1 ω t ht
  let K := |A|+|D|+M.mu 0+2
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg A, abs_nonneg D,M.mu_pos 0]
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hCoe : ∀ᶠ n in atTop, |a n| ≤ K ∧ |b n| ≤ K ∧ M.muR n 0 ≤ K := by
    have f₀ := (tendsto_order.1 ha.abs).2 K (by dsimp [K]; linarith [abs_nonneg D,M.mu_pos 0])
    have f₁ := (tendsto_order.1 hb.abs).2 K (by dsimp [K]; linarith [abs_nonneg A,M.mu_pos 0])
    have f₂ := (tendsto_order.1 (M.a31_iv 0)).2 K (by dsimp [K]; linarith [abs_nonneg A,abs_nonneg D])
    filter_upwards [f₀,f₁,f₂] with n h₀ h₁ h₂ using ⟨h₀.le,h₁.le,h₂.le⟩
  have hXF (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => M.P) P' := by
    simpa only [X,W,R,V,sub_eq_add_neg] using
      reflected_finite_observations_from_coupling M.P P' x z hXc hXm hZ hCouple a b A D ha hb q τ hτ
  have hXM := reflected_process_modulus M.P x hBdd hMod a b K hK0 (hCoe.mono fun _ h => ⟨h.1,h.2.1⟩)
  let e (n : ℕ) := (M.threshold c n:ℝ)/M.r n
  have he0 (n : ℕ) : 0 ≤ e n := div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (M.r_ge n))
  have heLim : Tendsto e atTop (𝓝 0) := by
    have hlo : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hup : Tendsto (fun n => c * (Real.log (M.r n)/M.r n)) atTop (𝓝 0) := by
      simpa using (hlo.comp M.r_tendsto).const_mul c
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup he0
    intro n
    dsimp [e]
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (Nat.floor_le (mul_nonneg hc.le (Real.log_nonneg (M.r_ge n))))
      (zero_le_one.trans (M.r_ge n))
  have hApprox (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc (0:ℝ) (H:ℝ), ε ≤ ‖Y n ω t-X n ω t‖}) atTop (𝓝 0) := by
    let L := 4*K^2
    have hL : 0 < L := by dsimp [L]; positivity
    have hL1 : 1 ≤ L := by dsimp [L]; nlinarith
    let δ := ε/(4*L)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδe : (δ+δ)*L = ε/2 := by dsimp [δ]; field_simp <;> norm_num
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hResidual H (Nat.cast_nonneg _) δ hδ) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hElig,hCoe,heLim.eventually_lt_const hδ] with n hn hk he
    apply measure_mono
    rintro ω ⟨t,ht,hw⟩
    by_contra hout
    let q := M.Qhat n (T n) ω t 0
    let i := M.Ihat n (T n) ω t 0
    have hR0 := threshold_state_reflection_approximation M c n (T n) (hT n hn).1 (hT n hn).2 ω t ht.1
    have hsum : |q| + |i| < δ := by
      have hSup : ENNReal.ofReal (|q|+|i|) ≤ supDist (fun t => ![M.Qhat n (T n) ω t 0,M.Ihat n (T n) ω t 0])
          (fun _ => 0) H := by
        apply le_iSup_of_le t
        apply le_iSup_of_le ht
        simp [Fin.sum_univ_two,q,i]
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 (hSup.trans_lt (lt_of_not_ge hout))
    have ha0 : 0 ≤ a n := inv_nonneg.2 (div_nonneg (M.muR_pos n 1).le (M.muR_pos n 2).le)
    have hb0 : 0 ≤ b n := inv_nonneg.2 (M.muR_pos n 1).le
    have hAK : a n ≤ K := by simpa only [abs_of_nonneg ha0] using hk.1
    have hBK : b n ≤ K := by simpa only [abs_of_nonneg hb0] using hk.2.1
    have h0 : 0 ≤ M.muR n 0 := (M.muR_pos n 0).le
    have hBound := mul_le_mul_of_nonneg_right (by linarith [hsum,he] : |q|+|i|+e n ≤ δ+δ) hL.le
    have hNorm : ‖Y n ω t-X n ω t‖ ≤ L*(|q|+|i|+e n) := by
      rw [pi_norm_le_iff_of_nonneg (mul_nonneg hL.le (add_nonneg (add_nonneg (abs_nonneg q) (abs_nonneg i)) (he0 n)))]
      intro j
      have hx : x n ω = M.workloadInput n (T n) ω := by funext s; simp [x,show G n from hn]
      have hden₀ : (2*M.muR n 0*i+e n+q) / M.poolingWeight n ≤ L*(|q|+|i|+e n) := by
        have hi := (mul_le_mul_of_nonneg_left (le_abs_self i) h0).trans
          (mul_le_mul_of_nonneg_right hk.2.2 (abs_nonneg i))
        rw [div_eq_mul_inv,←show a n = (M.poolingWeight n)⁻¹ from rfl]
        calc
          _ ≤ (2*K*|i|+e n+|q|)*K := mul_le_mul
            (by linarith [le_abs_self q,hi]) hAK ha0 (add_nonneg (add_nonneg (by positivity) (he0 n)) (abs_nonneg q))
          _ ≤ _ := by
            dsimp [L]
            have hh₁ : K ≤ K^2 := by nlinarith
            nlinarith [mul_nonneg (sub_nonneg.2 hh₁) (abs_nonneg q), mul_nonneg (sub_nonneg.2 hh₁) (he0 n),
              mul_nonneg (sq_nonneg K) (abs_nonneg i),
              mul_nonneg (sq_nonneg K) (abs_nonneg q),mul_nonneg (sq_nonneg K) (he0 n)]
      have hden₁ : (M.muR n 0*i+e n) / M.muR n 1 ≤ L*(|q|+|i|+e n) := by
        have hi := (mul_le_mul_of_nonneg_left (le_abs_self i) h0).trans
          (mul_le_mul_of_nonneg_right hk.2.2 (abs_nonneg i))
        rw [div_eq_mul_inv,←show b n = (M.muR n 1)⁻¹ from rfl]
        calc
          _ ≤ (K*|i|+e n)*K := mul_le_mul (by linarith [hi]) hBK hb0 (add_nonneg (mul_nonneg hK0.le (abs_nonneg i)) (he0 n))
          _ ≤ _ := by
            dsimp [L]
            have hh₁ : K ≤ K^2 := by nlinarith
            nlinarith [mul_nonneg (sq_nonneg K) (abs_nonneg q),mul_nonneg (sub_nonneg.2 hh₁) (he0 n),
              mul_nonneg (sq_nonneg K) (abs_nonneg i),
              mul_nonneg (sq_nonneg K) (abs_nonneg q),mul_nonneg (sq_nonneg K) (he0 n)]
      fin_cases j
      · have hco : |q| ≤ L*(|q|+|i|+e n) := by
          calc
            _ ≤ L*|q| := by nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (abs_nonneg q)]
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg i,he0 n]) hL.le
        simpa [Y,X,G,hn,q,Real.norm_eq_abs] using hco
      · simp only [Y,X,if_pos (show G n from hn),Pi.sub_apply,Real.norm_eq_abs,hx,R,V,a]
        exact (by simpa [div_eq_mul_inv,mul_comm] using hR0.1.trans hden₀)
      · have hco : |i| ≤ L*(|q|+|i|+e n) := by
          calc
            _ ≤ L*|i| := by nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (abs_nonneg i)]
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg q,he0 n]) hL.le
        simpa [Y,X,G,hn,i,Real.norm_eq_abs] using hco
      · simp only [Y,X,if_pos (show G n from hn),Pi.sub_apply,Real.norm_eq_abs,hx,b,V]
        exact (by simpa [div_eq_mul_inv,mul_comm] using hR0.2.trans hden₁)
    linarith [hBound.trans_eq hδe, show L*(|q|+|i|+e n) = (|q|+|i|+e n)*L by ring]
  obtain ⟨hYF,hYM⟩ := approximate_process_limits M.P P' X Y W hYm hXF
    (by simpa only [X,R,V,sub_eq_add_neg] using hXM) hApprox
  obtain ⟨Λ,mΛ,Q,U,F,hQ,hLaw,hLim,hCad,hConv⟩ :=
    coupling_from_ae_process_limits M.P P' Y W hYc hWc hYF hYM
  have hW (ω : Ω') (t : ℝ) :
      W ω t = ![0,M.Qstar B ω t 1,0,M.Istar B ω t 1] := by
    simp [W,A,D,R,V,z,SystemSequence.Qstar,SystemSequence.Istar,SystemSequence.Wstar,
      SystemSequence.Vstar,div_eq_mul_inv,mul_comm]
  refine ⟨Λ,mΛ,Q,U,F,hQ,?_,?_,hCad,hConv⟩
  · filter_upwards [hElig,hLaw] with n hn hl
    simpa only [Y,if_pos (show G n from hn)] using hl
  · simpa only [hW] using hLim
