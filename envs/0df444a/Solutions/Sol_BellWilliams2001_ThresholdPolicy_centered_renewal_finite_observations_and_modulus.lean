-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.centered_renewal_finite_observations_and_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:36.84937+00:00
-- url     : https://prove2.me/submissions/6681339f-4752-4fc1-a1d2-2c256b33f37e

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_epoch_donsker
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_inverse_approximation_in_probability
import Theorems.Thm_ManyServerQED_Scheduling_uniform_path_approximation_transfers_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law

open MeasureTheory ProbabilityTheory Filter Topology Set DurrettProbability
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

private theorem interp_grid {Ω : Type*} {X : ℕ → Ω → ℝ} {m j : ℕ}
    (hj : j ≤ m) (ω : Ω) :
    walkInterp X m ω j = ∑ i ∈ Finset.range j, X i ω := by
  unfold walkInterp
  rw [← Finset.sum_range_add_sum_Ico _ hj]
  have ha : (∑ i ∈ Finset.range j, X i ω*max 0 (min 1 ((j:ℝ)-i))) =
      ∑ i ∈ Finset.range j, X i ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hh : (1:ℝ) ≤ (j:ℝ)-i := by
      have hi' : (i:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hi)
      linarith
    rw [min_eq_left hh,max_eq_right zero_le_one,mul_one]
  have hb : (∑ i ∈ Finset.Ico j m, X i ω*max 0 (min 1 ((j:ℝ)-i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hh : (j:ℝ)-(i:ℝ) ≤ 0 :=
      sub_nonpos.mpr (by exact_mod_cast (Finset.mem_Ico.1 hi).1)
    rw [max_eq_left ((min_le_right _ _).trans hh),mul_zero]
  rw [ha,hb,add_zero]

set_option maxHeartbeats 650000 in
private theorem renewal_grid_algebra {Ω : Type*} (V : ℕ → Ω → ℝ)
    (s : ℝ) (hs : 0 < s) (J n : ℕ) (hJ : 0 < J) (hn : 0 < n) :
    ∀ ω (j : ℕ), (j:ℝ)/n ≤ J →
      (s*Real.sqrt (J:ℝ)) *
        walkPath (fun a ω => (V a ω-1)/s) (J*n) ω
          (projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ))) =
        ((∑ a ∈ Finset.range j,V a ω)-j)/Real.sqrt n := by
  intro ω j hj
  have hjR : 0 ≤ ((j:ℝ)/n)/(J:ℝ) := by positivity
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  have hJ1 : ((j:ℝ)/n)/(J:ℝ) ≤ 1 := (div_le_one hJR).2 hj
  have hProj : ((projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ)) :
        Icc (0:ℝ) 1) : ℝ) = ((j:ℝ)/n)/(J:ℝ) := by
    simp [Set.projIcc,max_eq_right hjR,min_eq_right hJ1]
  have hIdx : j ≤ J*n := by
    exact_mod_cast ((div_le_iff₀ hN).1 hj)
  have hMul : ((J*n:ℕ):ℝ)*(((j:ℝ)/n)/(J:ℝ)) = j := by
    push_cast
    field_simp
  let X (a : ℕ) (ω : Ω) := (V a ω-1)/s
  change s*Real.sqrt (J:ℝ) * (walkInterp X (J*n) ω
    (((J*n:ℕ):ℝ) * ((projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ)) : Icc (0:ℝ) 1):ℝ)) /
    Real.sqrt ((J*n:ℕ):ℝ)) = _
  rw [hProj,hMul,interp_grid hIdx,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg J)]
  simp only [X,← Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  field_simp [(Real.sqrt_pos.2 hN).ne',(Real.sqrt_pos.2 hJR).ne',hs.ne']
  <;> ring

private theorem approximate_path_fdd {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    {m : ℕ} (d : ℕ → Fin m → ℝ) (e : Fin m → ℝ)
    (hd : Tendsto d atTop (𝓝 e)) (c : ℝ)
    (Q : ℕ → Ω → Fin m → ℝ) (hQ : ∀ n, AEMeasurable (Q n) P)
    (hA : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ i : Fin m,
      ε ≤ |Q n ω i - c*Y n ω (Set.projIcc 0 1 zero_le_one (d n i))|}) atTop (𝓝 0)) :
    TendstoInDistribution Q atTop
      (fun ω i => c * Z ω (Set.projIcc 0 1 zero_le_one (e i))) (fun _ => P) P' := by
  have hdIn : TendstoInMeasure P (fun n (_ : Ω) => d n) atTop (fun _ => e) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hd))
  let f (z : PathSpace × (Fin m → ℝ)) (i : Fin m) :=
    c*z.1 (Set.projIcc 0 1 zero_le_one (z.2 i))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply Continuous.const_mul
    have hg : Continuous (fun z : PathSpace × (Fin m → ℝ) =>
        Set.projIcc (0:ℝ) 1 zero_le_one (z.2 i)) :=
      continuous_projIcc.comp ((continuous_apply i).comp continuous_snd)
    exact continuous_eval.comp (continuous_fst.prodMk hg)
  let I (n : ℕ) (ω : Ω) := f (Y n ω,d n)
  have hIZ : TendstoInDistribution I atTop
      (fun ω i => c * Z ω (Set.projIcc 0 1 zero_le_one (e i))) (fun _ => P) P' :=
    hY.continuous_comp_prodMk_of_tendstoInMeasure_const hf hdIn
      (fun _ => measurable_const.aemeasurable)
  refine tendstoInDistribution_of_tendstoInMeasure_sub Q _ hIZ ?_ hQ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hA ε hε)
    (Eventually.of_forall (fun _ => zero_le)) (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  have hnot : ¬∀ i, ‖Q n ω i - I n ω i‖ < ε := by
    intro hh
    have he : ‖(Q - I) n ω - (0 : Ω → Fin m → ℝ) ω‖ < ε := by
      apply (pi_norm_lt_iff hε).2
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using hh
    exact (not_le_of_gt he) hω
  push Not at hnot
  obtain ⟨i,hi⟩ := hnot
  exact ⟨i,by simpa only [Real.norm_eq_abs] using hi⟩

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

private theorem unit_epoch_error {Ω : Type*} (V : ℕ → Ω → ℝ) (ω : Ω)
    (hV : ∀ j, V j ω = 1) (s : ℝ) (hs : 0 ≤ s) :
    |((renewalCount (fun j => ∑ i ∈ Finset.range j, V i ω) s).toNat : ℝ) - s| ≤ 1 := by
  simp only [hV,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  have hR : renewalCount (fun j : ℕ => (j:ℝ)) s = (⌊s⌋₊:ℕ∞) := by
    unfold renewalCount
    apply le_antisymm
    · refine iSup₂_le fun j hj => ?_
      exact_mod_cast (Nat.le_floor hj)
    · exact le_iSup₂_of_le ⌊s⌋₊ (Nat.floor_le hs) le_rfl
  rw [hR,ENat.toNat_natCast,abs_of_nonpos (sub_nonpos.2 (Nat.floor_le hs))]
  linarith [Nat.lt_floor_add_one s]

set_option maxHeartbeats 3200000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (V : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (V j)) (hind : iIndepFun V P)
    (hident : ∀ j, IdentDistrib (V j) (V 0) P P) (hLp : MemLp (V 0) 2 P)
    (hmean : ∫ ω, V 0 ω ∂P = 1) (hpos : ∀ j ω, 0 < V j ω)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 < a)
    (halim : Tendsto aN atTop (𝓝 a))
    (B : ℝ≥0 → Ω' → ℝ) (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    let X (n : ℕ) (ω : Ω) (t : ℝ) :=
      (((renewalCount (fun j => ∑ i ∈ Finset.range j, V i ω) ((m n:ℝ)*aN n*t)).toNat:ℝ)
        - (m n:ℝ)*aN n*t) / Real.sqrt (m n)
    let Z (ω : Ω') (t : ℝ) := Real.sqrt (a*variance (V 0) P) * B t.toNNReal ω
    (∀ (k : ℕ) (τ : Fin k → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P') ∧
    (∀ T ε η : ℝ, 0 ≤ T → 0 < ε → 0 < η → ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |X n ω t|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η) := by
  let e (ω : Ω) (j : ℕ) := ∑ i ∈ Finset.range j, V i ω
  let X (n : ℕ) (ω : Ω) (t : ℝ) :=
    (((renewalCount (e ω) ((m n:ℝ)*aN n*t)).toNat:ℝ) - (m n:ℝ)*aN n*t) / Real.sqrt (m n)
  let v := variance (V 0) P
  let Z (ω : Ω') (t : ℝ) := Real.sqrt (a*v) * B t.toNNReal ω
  have hM (n : ℕ) (t : ℝ) : Measurable (fun ω => X n ω t) :=
    ((renewal_eval_measurable V hmeas _).sub_const _).div_const _
  have hscale : Tendsto (fun n => 1/Real.sqrt (m n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hm))
  have hDon := renewal_epoch_donsker V hmeas hind hident hLp hmean B hB hBc
  have hnon : 0 ≤ v := variance_nonneg _ _
  rcases hnon.eq_or_lt with hzero | hvar
  · have hZero : ∀ᵐ ω ∂P, ∀ n t, 0 ≤ t → |X n ω t| ≤ 1/Real.sqrt (m n) := by
      filter_upwards [hDon.2 hzero.symm] with ω hω
      intro n t ht
      have hz := unit_epoch_error V ω hω ((m n:ℝ)*aN n*t) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (haN n)) ht)
      rw [show X n ω t = _ from rfl,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_div_of_nonneg_right hz (Real.sqrt_nonneg _)
    constructor
    · intro k τ hτ
      let Q (n : ℕ) (ω : Ω) (j : Fin k) := X n ω (τ j)
      have hQ (n : ℕ) : AEMeasurable (Q n) P :=
        (measurable_pi_lambda _ fun j => hM n (τ j)).aemeasurable
      have hz : TendstoInMeasure P Q atTop (0 : Ω → Fin k → ℝ) := by
        apply tendstoInMeasure_of_tendsto_ae (fun n => (hQ n).aestronglyMeasurable)
        filter_upwards [hZero] with ω hω
        rw [tendsto_pi_nhds]
        intro j
        apply squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hscale
        simpa only [Real.norm_eq_abs] using hω n (τ j) (hτ j)
      have h0 : AEMeasurable (fun _ : Ω' => (0 : Fin k → ℝ)) P' := aemeasurable_const
      have hzD := hz.tendstoInDistribution_of_aemeasurable hQ (aemeasurable_const (b := (0 : Fin k → ℝ)))
      have hh : TendstoInDistribution Q atTop (fun _ : Ω' => (0 : Fin k → ℝ)) (fun _ => P) P' := by
        refine ⟨hQ,h0,?_⟩
        have he : (⟨P.map (fun _ : Ω => (0 : Fin k → ℝ)),
          Measure.isProbabilityMeasure_map aemeasurable_const⟩ : ProbabilityMeasure (Fin k → ℝ)) =
          ⟨P'.map (fun _ : Ω' => (0 : Fin k → ℝ)),Measure.isProbabilityMeasure_map h0⟩ :=
          Subtype.ext (by simp [Measure.map_const])
        exact he ▸ hzD.tendsto
      exact hh.congr (fun _ => EventuallyEq.rfl)
        (Eventually.of_forall fun ω => funext (fun j => by change 0 = Z ω (τ j); simp only [Z,hzero.symm,mul_zero,Real.sqrt_zero,zero_mul]))
    · intro T ε η hT hε hη
      refine ⟨1,zero_lt_one,1,zero_lt_one,?_⟩
      filter_upwards [(tendsto_order.1 hscale).2 (min 1 (ε/2)) (lt_min zero_lt_one (by positivity))] with n hn
      refine le_trans (le_of_eq (measure_mono_null ?_ (ae_iff.1 hZero))) zero_le
      intro ω hω hAll
      rcases hω with ⟨t,ht,he⟩ | ⟨s,hs,t,ht,_,he⟩
      · exact not_le_of_gt ((hAll n t ht.1).trans_lt ((lt_min_iff.1 hn).1)) he
      · have hb := abs_sub (X n ω s) (X n ω t)
        linarith only [hb,he,hAll n s hs.1,hAll n t ht.1,(lt_min_iff.1 hn).2]
  have hBuild (T : ℝ) (hT : 0 ≤ T) : ∃ J : ℕ, (a+1)*T+3 < J := exists_nat_gt _
  let Y (J n : ℕ) := walkPath (fun j ω => (V j ω-1)/Real.sqrt v) (J*m n)
  have hWeak (J : ℕ) (hJ : 1 ≤ J) :
      TendstoInDistribution (Y J) atTop (brownianPath B) (fun _ => P) P' := by
    have hR : Tendsto (fun n : ℕ => J*m n) atTop atTop :=
      tendsto_atTop_mono (fun n => by simpa only [one_mul] using Nat.mul_le_mul_right (m n) hJ) hm
    have hh := hDon.1 hvar
    exact ⟨fun n => hh.forall_aemeasurable (J*m n),hh.aemeasurable_limit,hh.tendsto.comp hR⟩
  have hApprox (T : ℝ) (hT : 0 ≤ T) (J : ℕ) (hJ : (a+1)*T+3 < J) :
      ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T, ε ≤
        |X n ω t + (Real.sqrt v*Real.sqrt (J:ℝ))*Y J n ω
          (projIcc 0 1 zero_le_one (aN n*t/(J:ℝ)))|}) atTop (𝓝 0) := by
    have hJr : (0:ℝ) < J := (show 0 < (a+1)*T+3 by nlinarith).trans hJ
    have hJn : 0 < J := by exact_mod_cast hJr
    have hS : 0 < Real.sqrt v := Real.sqrt_pos.2 hvar
    have hH : ∀ᶠ n in atTop, aN n*T+3 ≤ (J:ℝ) := by
      filter_upwards [(tendsto_order.1 halim).2 _ (by linarith : a < a+1)] with n hn
      exact (add_le_add_left (mul_le_mul_of_nonneg_right hn.le hT) _).trans hJ.le
    have he (ω : Ω) : StrictMono (e ω) := by
      apply strictMono_nat_of_lt_succ
      intro j
      dsimp only [e]
      rw [Finset.sum_range_succ]
      exact lt_add_of_pos_right _ (hpos j ω)
    exact renewal_inverse_approximation_in_probability (Y J) (brownianPath B)
      (hWeak J hJn) m hm (Real.sqrt v*Real.sqrt (J:ℝ)) J
      (mul_pos hS (Real.sqrt_pos.2 hJr)) hJr (fun _ => e)
      (fun _ ω => he ω) (fun _ ω => by simp [e]) aN haN T hT hH
      (fun n hn ω j hj => renewal_grid_algebra V (Real.sqrt v) hS J (m n) hJn hn ω j hj)
  constructor
  · intro k τ hτ
    let Q (n : ℕ) (ω : Ω) (j : Fin k) := X n ω (τ j)
    have hQ (n : ℕ) : AEMeasurable (Q n) P :=
      (measurable_pi_lambda _ fun j => hM n (τ j)).aemeasurable
    obtain ⟨T,hT,hτT⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ j, τ j ≤ T := by
      let T := ∑ j, max (τ j) 0
      exact ⟨T,Finset.sum_nonneg (fun _ _ => le_max_right _ _),fun j =>
        (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (τ j) 0)
          (fun _ _ => le_max_right _ _) (Finset.mem_univ _))⟩
    obtain ⟨J,hJ⟩ := hBuild T hT
    have hJ0 : 0 < (J:ℝ) := (by nlinarith : 0 < (a+1)*T+3).trans hJ
    have hJn : 1 ≤ J := by exact_mod_cast hJ0
    let s := Real.sqrt v
    let c := -(s*Real.sqrt (J:ℝ))
    let d (n : ℕ) (j : Fin k) := aN n*τ j/(J:ℝ)
    let d₀ (j : Fin k) := a*τ j/(J:ℝ)
    have hd : Tendsto d atTop (𝓝 d₀) := by
      apply tendsto_pi_nhds.2
      intro j
      exact (halim.mul tendsto_const_nhds).div_const _
    have hA (ε : ℝ) (hε : 0 < ε) : Tendsto (fun n => P {ω | ∃ j : Fin k,
        ε ≤ |Q n ω j-c*Y J n ω (projIcc 0 1 zero_le_one (d n j))|}) atTop (𝓝 0) := by
      have h := hApprox T hT J hJ ε hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => measure_mono ?_)
      rintro ω ⟨j,hj⟩
      exact ⟨τ j,⟨hτ j,hτT j⟩,by simpa only [c,neg_mul,sub_neg_eq_add] using hj⟩
    have hLaw := approximate_path_fdd (Y J) (brownianPath B) (hWeak J hJn) d d₀ hd c Q hQ hA
    have hD (j : Fin k) : d₀ j ∈ Icc (0:ℝ) 1 := by
      have hBound := mul_le_mul_of_nonneg_left (hτT j) ha.le
      have hW := mul_le_mul_of_nonneg_right (show a ≤ a+1 by linarith) hT
      exact ⟨div_nonneg (mul_nonneg ha.le (hτ j)) hJ0.le, (div_le_one hJ0).2 (by linarith)⟩
    let b : ℝ≥0 := (a/(J:ℝ)).toNNReal
    have hb : 0 < a/(J:ℝ) := div_pos ha hJ0
    have hbR : (b:ℝ) = a/(J:ℝ) := Real.coe_toNNReal _ hb.le
    have hbNN : b ≠ 0 := by
      intro h
      exact hb.ne' (hbR.symm.trans (by rw [h]; rfl))
    let C (t : ℝ≥0) (ω : Ω') := (Real.sqrt (b:ℝ))⁻¹ * (-B (b*t) ω)
    have hC : IsBrownianReal C P' := hB.neg.smul hbNN
    have hCoef : Real.sqrt (a*v) = (s*Real.sqrt (J:ℝ))*Real.sqrt (b:ℝ) := by
      rw [mul_assoc,← Real.sqrt_mul (Nat.cast_nonneg J),hbR]
      rw [show (J:ℝ)*(a/(J:ℝ)) = a by field_simp]
      rw [← Real.sqrt_mul hnon,mul_comm v]
    let R (ω : Ω') (j : Fin k) := Real.sqrt (a*v)*C (τ j).toNNReal ω
    have hRval (ω : Ω') (j : Fin k) :
        c * brownianPath B ω (projIcc 0 1 zero_le_one (d₀ j)) = R ω j := by
      have htime : (⟨(projIcc 0 1 zero_le_one (d₀ j) : Icc (0:ℝ) 1),
          (projIcc 0 1 zero_le_one (d₀ j)).2.1⟩ : ℝ≥0) = b*(τ j).toNNReal := by
        apply Subtype.ext
        change ((projIcc 0 1 zero_le_one (d₀ j) : Icc (0:ℝ) 1) : ℝ) = (b:ℝ)*(τ j).toNNReal
        rw [hbR,Real.coe_toNNReal _ (hτ j)]
        simp only [projIcc,max_eq_right (hD j).1,min_eq_right (hD j).2]
        dsimp [d₀]
        ring
      unfold brownianPath toPath
      simp only [hBc ω,dite_true,ContinuousMap.coe_mk]
      rw [htime]
      dsimp [R,C,c]
      rw [hCoef]
      have hbs : Real.sqrt (b:ℝ) ≠ 0 := (Real.sqrt_pos.2 (hbR ▸ hb)).ne'
      field_simp
    have hRlaw := hLaw.congr (fun _ => EventuallyEq.rfl)
      (Eventually.of_forall fun ω => funext (hRval ω))
    have hId := ManyServerQED.Scheduling.brownian_weighted_finite_observation_law
      hC.toIsPreBrownianReal hB.toIsPreBrownianReal
      (fun j => (τ j).toNNReal) (fun _ => Real.sqrt (a*v))
    refine ⟨hRlaw.forall_aemeasurable,hId.aemeasurable_snd,?_⟩
    have hEq : (⟨P'.map R,Measure.isProbabilityMeasure_map hRlaw.aemeasurable_limit⟩ :
        ProbabilityMeasure (Fin k → ℝ)) =
        ⟨P'.map (fun ω j => Z ω (τ j)),Measure.isProbabilityMeasure_map hId.aemeasurable_snd⟩ :=
      Subtype.ext hId.map_eq
    exact hEq ▸ hRlaw.tendsto
  · intro T ε η hT hε hη
    obtain ⟨J,hJ⟩ := hBuild T hT
    have hJ0 : 0 < (J:ℝ) := (by nlinarith : 0 < (a+1)*T+3).trans hJ
    have hJn : 1 ≤ J := by exact_mod_cast hJ0
    let c := -(Real.sqrt v * Real.sqrt (J:ℝ))
    let L := (a+1)/(J:ℝ)
    let d (n : ℕ) (t : ℝ) := projIcc 0 1 zero_le_one (aN n*t/(J:ℝ))
    have hL : 0 < L := div_pos (by linarith) hJ0
    have hD : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
        dist (d n s) (d n t) ≤ L*|s-t| := by
      filter_upwards [(tendsto_order.1 halim).2 _ (show a < a+1 by linarith)] with n hn
      have hproj (s : ℝ) (hs : s ∈ Icc 0 T) : (d n s : ℝ) = aN n*s/(J:ℝ) := by
        have h0 : 0 ≤ aN n*s/(J:ℝ) := div_nonneg (mul_nonneg (haN n) hs.1) hJ0.le
        have h1 : aN n*s/(J:ℝ) ≤ 1 := by
          apply (div_le_one hJ0).2
          have hb := mul_le_mul (show aN n ≤ a+1 from hn.le) hs.2 hs.1
            (by linarith : 0 ≤ a+1)
          linarith
        simp [d,projIcc,max_eq_right h0,min_eq_right h1]
      intro s hs t ht
      rw [Subtype.dist_eq,Real.dist_eq,hproj s hs,hproj t ht,
        show aN n*s/(J:ℝ)-aN n*t/(J:ℝ) = (aN n/(J:ℝ))*(s-t) by ring,
        abs_mul,abs_of_nonneg (div_nonneg (haN n) hJ0.le)]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn.le hJ0.le) (abs_nonneg _)
    exact ManyServerQED.Scheduling.uniform_path_approximation_transfers_norm_and_modulus_bounds
      X (Y J) (brownianPath B) (hWeak J hJn) T c L hL d hD
      (fun w hw => by simpa only [c,neg_mul,sub_neg_eq_add] using hApprox T hT J hJ w hw)
      ε η hε hη
