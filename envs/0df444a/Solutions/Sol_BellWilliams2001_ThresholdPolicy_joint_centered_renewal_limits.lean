-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.joint_centered_renewal_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:08:14.32801+00:00
-- url     : https://prove2.me/submissions/a189b922-677c-45e0-99b9-be811994591d

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_centered_renewal_finite_observations_and_modulus
import Theorems.Thm_ManyServerQED_Scheduling_joint_weak_limit_of_independent_finite_family
import Theorems.Thm_ManyServerQED_Scheduling_finite_coordinate_modulus_controls_vector_modulus

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling
open scoped ENNReal NNReal

private theorem renewal_eval_measurable {Ω : Type*} [MeasurableSpace Ω]
    (V : ℕ → Ω → ℝ) (hM : ∀ j, Measurable (V j)) (s : ℝ) :
    Measurable (fun ω => ((renewalCount (fun j => ∑ i ∈ Finset.range j, V i ω) s).toNat : ℝ)) := by
  let R (ω : Ω) := renewalCount (fun j => ∑ i ∈ Finset.range j, V i ω) s
  have hL (a : ℕ∞) : MeasurableSet {ω | R ω ≤ a} := by
    have hEq : {ω | R ω ≤ a} = ⋂ j : ℕ, {ω | (∑ i ∈ Finset.range j, V i ω) ≤ s → (j : ℕ∞) ≤ a} := by
      ext ω
      simp only [mem_ofPred_eq,mem_iInter,R,renewalCount,iSup_le_iff]
    rw [hEq]
    apply MeasurableSet.iInter
    intro j
    by_cases hj : (j : ℕ∞) ≤ a
    · simp [hj]
    · simp only [hj,imp_false,not_le]
      exact measurableSet_lt (measurable_const (a := s))
        (Finset.measurable_sum (Finset.range j) (fun i _ => hM i))
  have hLt (a : ℕ∞) : MeasurableSet {ω | R ω < a} := by
    have he : {ω | R ω < a} = ⋃ b : ℕ∞, ⋃ (_ : b < a), {ω | R ω ≤ b} := by
      ext ω
      simp only [mem_ofPred_eq,mem_iUnion]
      exact ⟨fun h => ⟨R ω,h,le_rfl⟩, fun ⟨_,hb,h⟩ => h.trans_lt hb⟩
    rw [he]
    exact MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ => hL b))
  have hR : Measurable R := by
    apply measurable_to_countable'
    intro a
    have he : R ⁻¹' {a} = {ω | R ω ≤ a} \ {ω | R ω < a} := by
      ext ω
      simp only [mem_preimage,mem_singleton_iff,Set.mem_sdiff,mem_ofPred_eq,not_lt]
      exact le_antisymm_iff
    rw [he]
    exact (hL a).diff (hLt a)
  exact (measurable_of_countable (fun j : ℕ∞ => (j.toNat:ℝ))).comp hR


set_option maxHeartbeats 2700000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {k : ℕ} (V : Fin k → ℕ → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (V i j)) (hind : ∀ i, iIndepFun (V i) P)
    (hident : ∀ i j, IdentDistrib (V i j) (V i 0) P P)
    (hLp : ∀ i, MemLp (V i 0) 2 P) (hmean : ∀ i, ∫ ω, V i 0 ω ∂P = 1)
    (hpos : ∀ i j ω, 0 < V i j ω)
    (hIndV : iIndepFun (fun i ω j => V i j ω) P)
    (r : ℕ → ℝ) (hr : ∀ n, 1 ≤ r n) (hrlim : Tendsto r atTop atTop)
    (aN : ℕ → Fin k → ℝ) (haN : ∀ n i, 0 ≤ aN n i)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    (halim : ∀ i, Tendsto (fun n => aN n i) atTop (𝓝 (a i)))
    (B : Fin k → ℝ≥0 → Ω' → ℝ) (hB : ∀ i, IsBrownianReal (B i) P')
    (hBc : ∀ i ω, Continuous (fun t => B i t ω))
    (hIndB : iIndepFun (fun i ω t => B i t ω) P') :
    let X (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
      (((renewalCount (fun j => ∑ l ∈ Finset.range j, V i l ω) (aN n i*(r n^2*t))).toNat:ℝ)
        - aN n i*(r n^2*t)) / r n
    let Z (ω : Ω') (t : ℝ) (i : Fin k) := Real.sqrt (a i*variance (V i 0) P)*B i t.toNNReal ω
    (∀ (m : ℕ) (τ : Fin m → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) := by
  let m (n : ℕ) := Nat.ceil (r n^2)
  have hSq : Tendsto (fun n => r n^2) atTop atTop := tendsto_pow_atTop (by decide : 2 ≠ 0) |>.comp hrlim
  have hm : Tendsto m atTop atTop := tendsto_nat_ceil_atTop.comp hSq
  have h_r (n : ℕ) : 0 < r n := zero_lt_one.trans_le (hr n)
  have h_m (n : ℕ) : (0:ℝ) < m n := (sq_pos_of_pos (h_r n)).trans_le (Nat.le_ceil _)
  let b (n : ℕ) : ℝ := (m n:ℝ)/(r n)^2
  have hb : Tendsto b atTop (𝓝 1) := tendsto_nat_ceil_div_atTop.comp hSq
  have hbInv : Tendsto (fun n => (b n)⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hb.inv₀ one_ne_zero
  let d (n : ℕ) := Real.sqrt (b n)
  have hd : Tendsto d atTop (𝓝 1) := by simpa only [Real.sqrt_one] using hb.sqrt
  have hD (n : ℕ) : d n = Real.sqrt (m n:ℝ)/r n := by
    dsimp [d,b]
    rw [Real.sqrt_div (Nat.cast_nonneg _),Real.sqrt_sq (h_r n).le]
  have hd0 (n : ℕ) : 0 ≤ d n := Real.sqrt_nonneg _
  let aM (n : ℕ) (i : Fin k) := aN n i * (b n)⁻¹
  have haM (n : ℕ) (i : Fin k) : 0 ≤ aM n i :=
    mul_nonneg (haN n i) (inv_nonneg.2 (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have hAL (i : Fin k) : Tendsto (fun n => aM n i) atTop (𝓝 (a i)) := by
    simpa only [mul_one,Pi.mul_def] using (halim i).mul hbInv
  have hclock (n : ℕ) (i : Fin k) (t : ℝ) : (m n:ℝ)*aM n i*t = aN n i * (r n^2*t) := by
    dsimp [aM,b]
    field_simp [(h_m n).ne',(h_r n).ne']
    <;> ring
  let X (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    (((renewalCount (fun j => ∑ l ∈ Finset.range j, V i l ω) (aN n i*(r n^2*t))).toNat:ℝ)
      - aN n i*(r n^2*t)) / r n
  let Z (ω : Ω') (t : ℝ) (i : Fin k) := Real.sqrt (a i*variance (V i 0) P)*B i t.toNNReal ω
  let Y (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    (((renewalCount (fun j => ∑ l ∈ Finset.range j, V i l ω) ((m n:ℝ)*aM n i*t)).toNat:ℝ)
      - (m n:ℝ)*aM n i*t) / Real.sqrt (m n)
  have hx (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) : X n ω t i = d n * Y n ω t i := by
    rw [hD]
    dsimp [X,Y]
    rw [hclock]
    exact (by field_simp [(Real.sqrt_pos.2 (h_m n)).ne',(h_r n).ne'])
  have hSingle (i : Fin k) :=
    centered_renewal_finite_observations_and_modulus (V i) (hmeas i) (hind i) (hident i) (hLp i)
      (hmean i) (hpos i) m hm (fun n => aM n i) (fun n => haM n i) (a i) (ha i) (hAL i)
      (B i) (hB i) (hBc i)
  constructor
  · intro q τ hτ
    let E := EuclideanSpace ℝ (Fin q)
    let e : (Fin q → ℝ) ≃L[ℝ] E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => ℝ)).symm
    let U (n : ℕ) (i : Fin k) (v : ℕ → ℝ) (j : Fin q) :=
      (((renewalCount (fun l => ∑ p ∈ Finset.range l, v p) ((m n:ℝ)*aM n i*τ j)).toNat:ℝ)
       - (m n:ℝ)*aM n i*τ j) / Real.sqrt (m n)
    let f (i : Fin k) (n : ℕ) (ω : Ω) := e (fun j => Y n ω (τ j) i)
    let z (i : Fin k) (ω : Ω') := e (fun j => Z ω (τ j) i)
    have hInd (n : ℕ) : iIndepFun (fun i => f i n) P := by
      exact hIndV.comp (fun i v => e (U n i v)) (fun i => e.continuous.measurable.comp
        (measurable_pi_lambda _ fun j => ((renewal_eval_measurable
          (fun p (v : ℕ → ℝ) => v p) measurable_pi_apply _).sub_const _).div_const _))
    have hz : iIndepFun z P' := hIndB.comp
      (fun i (v : ℝ≥0 → ℝ) => e (fun j => Real.sqrt (a i*variance (V i 0) P) * v (τ j).toNNReal))
      (fun i => e.continuous.measurable.comp
        (measurable_pi_lambda _ fun j => (measurable_pi_apply (τ j).toNNReal).const_mul _))
    have hMarg (i : Fin k) : TendstoInDistribution (f i) atTop (z i) (fun _ => P) P' :=
      ((hSingle i).1 q τ hτ).continuous_comp e.continuous
    have hJ := joint_weak_limit_of_independent_finite_family f z hMarg (Eventually.of_forall hInd) hz
    let g (u : (Fin k → E) × ℝ) (j : Fin q) (i : Fin k) := u.2 * e.symm (u.1 i) j
    have hg : Continuous g := continuous_pi fun j => continuous_pi fun i => continuous_snd.mul
      ((continuous_apply j).comp (e.symm.continuous.comp ((continuous_apply i).comp continuous_fst)))
    have hdM : TendstoInMeasure P (fun n (_ : Ω) => d n) atTop (fun _ => (1:ℝ)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hd))
    have h := hJ.continuous_comp_prodMk_of_tendstoInMeasure_const hg hdM (fun _ => aemeasurable_const)
    change TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
      (fun ω j => Z ω (τ j)) (fun _ => P) P'
    simpa only [g,f,z,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,one_mul,←hx] using h
  · intro T
    apply finite_coordinate_modulus_controls_vector_modulus P X T
    intro i ε η hε hη
    obtain ⟨A,_,δ,hδ,h⟩ := (hSingle i).2 T (ε/2) η (Nat.cast_nonneg _) (by positivity) hη
    refine ⟨δ,hδ,?_⟩
    filter_upwards [h,(tendsto_order.1 hd).2 2 (by norm_num)] with n hn hdn
    refine (measure_mono ?_).trans hn
    rintro ω ⟨s,hs,t,ht,hst,hb⟩
    refine Or.inr ⟨s,hs,t,ht,hst,?_⟩
    rw [hx,hx,←mul_sub,abs_mul,abs_of_nonneg (hd0 n)] at hb
    have hh := mul_le_mul_of_nonneg_right hdn.le (abs_nonneg (Y n ω s i - Y n ω t i))
    change ε/2 ≤ |Y n ω s i-Y n ω t i|
    linarith
