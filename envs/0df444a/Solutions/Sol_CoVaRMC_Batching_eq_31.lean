-- Prove2me | solution 1 for CoVaRMC.Batching.eq_31
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:31:43.744874+00:00
-- url     : https://prove2.me/submissions/be6b1301-b900-43a4-86c0-ef00f22c3c9e

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_CoVaRMC_Batching_eq_30
import Theorems.Thm_CoVaRMC_Batching_lemma_4

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaREq31Aux


lemma measurableSet_sort_eq {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {ω | Tuple.sort (fun j => X j ω) = σ} := by
  have : {ω | Tuple.sort (fun j => X j ω) = σ} =
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≤ j → X (σ i) ω ≤ X (σ j) ω}) ∩
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i < j → X (σ i) ω = X (σ j) ω → σ i < σ j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (hX _) (hX _)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (hX _) (hX _)).compl
    · simp [hij]

lemma measurable_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X A : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hA : ∀ j, Measurable (A j)) (r : Fin N) :
    Measurable (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) := by
  have heq : (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) = fun ω =>
      ∑ σ : Equiv.Perm (Fin N),
        Set.indicator {ω | Tuple.sort (fun j => X j ω) = σ} (A (σ r)) ω := by
    funext ω
    rw [Finset.sum_eq_single (Tuple.sort (fun j => X j ω))]
    · simp
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hσ h.symm
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun σ _ =>
    (hA _).indicator (measurableSet_sort_eq X hX σ)

open CoVaRMC.Batching

lemma measurable_Yhat {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α : ℝ) (m i : ℕ) :
    Measurable (fun ω => Yhat S α m i ω) := by
  unfold Yhat
  by_cases hm : 0 < m
  · simp only [dif_pos hm, ImpactInvesting.Portfolio.inducedOrderStat]
    exact measurable_induced (fun j : Fin m => fun ω => (S (i, j) ω).1)
      (fun j : Fin m => fun ω => (S (i, j) ω).2) (fun j => (hSm _).fst) (fun j => (hSm _).snd) _
  · simp only [dif_neg hm]; exact measurable_const

lemma measurable_YBE {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α β : ℝ) (k m : ℕ) :
    Measurable (fun ω => YBE S α β k m ω) := by
  unfold YBE
  by_cases hk : 0 < k
  · simp only [dif_pos hk, ImpactInvesting.Portfolio.orderStat]
    exact measurable_induced (fun i : Fin k => fun ω => Yhat S α m i ω)
      (fun i : Fin k => fun ω => Yhat S α m i ω) (fun i => measurable_Yhat S hSm α m i)
      (fun i => measurable_Yhat S hSm α m i) _
  · simp only [dif_neg hk]; exact measurable_const

lemma measurable_FkHat {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α : ℝ) (k m : ℕ) (y : ℝ) :
    Measurable (fun ω => FkHat S α k m y ω) := by
  unfold FkHat empCDF
  refine measurable_const.mul ?_
  have : (fun ω => (((Finset.univ.filter fun i : Fin k => Yhat S α m i ω ≤ y).card : ℕ) : ℝ)) =
      fun ω => ∑ i : Fin k, Set.indicator {ω | Yhat S α m i ω ≤ y} (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : Yhat S α m i ω ≤ y <;> simp [h]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator (measurableSet_le (measurable_Yhat S hSm α m i) measurable_const)

/-- Standard normal cdf is continuous. -/
lemma continuous_Phi : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro x
  have hm : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have h2 := hm.leftLim_le (le_refl x)
  linarith

lemma Phi_neg (a : ℝ) : cdf (gaussianReal 0 1) (-a) = 1 - cdf (gaussianReal 0 1) a := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [cdf_eq_real, cdf_eq_real]
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have : (gaussianReal 0 1).real (Set.Iic (-a)) = (gaussianReal 0 1).real (Set.Ici a) := by
    conv_lhs => rw [← hmap]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x; simp
  rw [this, ← Set.Ioi_union_left, measureReal_union (by simp) (measurableSet_singleton a),
    measureReal_def (s := {a}), measure_singleton, ENNReal.toReal_zero, add_zero, ← Set.compl_Iic,
    measureReal_compl measurableSet_Iic]
  simp

end CoVaREq31Aux

open CoVaREq31Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop)
    (t : ℝ) :
    ∃ C : ℝ, ∀ᶠ ν in atTop,
      |(P {ω | √(k ν : ℝ) / Aconst D β v c * (YBE S α β (k ν) (m ν) ω - c) ≤ t}).toReal
          - cdf (gaussianReal 0 1) (-cmk P S α β c (Aconst D β v c) t (k ν) (m ν))|
        ≤ C / √(k ν : ℝ) := by
  obtain ⟨h30i, h30ii, h30iii⟩ := CoVaRMC.Batching.eq_30 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM
    hM1 hM2 P S hSm hSi hSl k m hk0 hm0 hk hm t
  set A := Aconst D β v c with hAdef
  set σ0 := √(β * (1 - β)) with hσ0
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.mpr (mul_pos hβ.1 (by linarith [hβ.2]))
  have hev : ∀ᶠ ν in atTop, σ0 / 2 < sigmaHat P S α (m ν) (yk c A t (k ν)) :=
    h30iii.eventually (lt_mem_nhds (by linarith))
  refine ⟨33 / 4 * 8 / σ0 ^ 3, ?_⟩
  filter_upwards [hev] with ν hν
  set s := sigmaHat P S α (m ν) (yk c A t (k ν)) with hsdef
  have hs : 0 < s := by linarith
  have hsk : 0 < √(k ν : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)
  set a := cmk P S α β c A t (k ν) (m ν) with hadef
  set Z : Ω → ℝ := fun ω => √(k ν : ℝ) / s *
    (FkHat S α (k ν) (m ν) (yk c A t (k ν)) ω - pHat P S α (m ν) (yk c A t (k ν))) with hZdef
  have hZm : Measurable Z :=
    measurable_const.mul ((measurable_FkHat S hSm α (k ν) (m ν) _).sub measurable_const)
  rw [h30i ν, h30ii ν hs]
  set Φ := cdf (gaussianReal 0 1) with hΦ
  set B := 33 / 4 * (1 / (s ^ 3 * √(k ν : ℝ))) with hBdef
  have hL4 : ∀ s' : ℝ, |P.real {ω | Z ω ≤ s'} - Φ s'| ≤ B := fun s' =>
    CoVaRMC.Batching.lemma_4 D α hα P S hSm hSi hSl (k ν) (m ν) (hk0 ν) (hm0 ν) _ hs s'
  have hBle : B ≤ 33 / 4 * 8 / σ0 ^ 3 / √(k ν : ℝ) := by
    have h3 : σ0 ^ 3 / 8 < s ^ 3 := by
      have := pow_lt_pow_left₀ hν (by linarith) (by norm_num : (3 : ℕ) ≠ 0)
      linarith [show (σ0 / 2) ^ 3 = σ0 ^ 3 / 8 by ring]
    rw [hBdef]
    have hσ3 : 0 < σ0 ^ 3 := pow_pos hσ0pos 3
    rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right h3 hsk]
  -- `P{Z < a}` is within `B` of `Φ a`
  have hup : P.real {ω | Z ω < a} ≤ Φ a + B := by
    have h1 : P.real {ω | Z ω < a} ≤ P.real {ω | Z ω ≤ a} :=
      measureReal_mono (fun ω (h : Z ω < a) => (le_of_lt h : Z ω ≤ a))
    have h2 := (abs_le.mp (hL4 a)).2
    linarith
  have hlow : Φ a - B ≤ P.real {ω | Z ω < a} := by
    have hT : Tendsto (fun δ => Φ (a - δ) - B) (𝓝[>] 0) (𝓝 (Φ a - B)) := by
      have : Tendsto (fun δ : ℝ => Φ (a - δ) - B) (𝓝 0) (𝓝 (Φ (a - 0) - B)) :=
        ((continuous_Phi.comp (continuous_const.sub continuous_id)).tendsto 0).sub
          tendsto_const_nhds
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    have h1 := (abs_le.mp (hL4 (a - δ))).1
    have h2 : P.real {ω | Z ω ≤ a - δ} ≤ P.real {ω | Z ω < a} :=
      measureReal_mono (fun ω (h : Z ω ≤ a - δ) => (by linarith : Z ω < a))
    linarith
  have hcompl : {ω | a ≤ Z ω} = {ω | Z ω < a}ᶜ := by
    ext ω; simp [not_lt]
  have hmeas : MeasurableSet {ω | Z ω < a} := measurableSet_lt hZm measurable_const
  have hP : (P {ω | a ≤ Z ω}).toReal = 1 - P.real {ω | Z ω < a} := by
    rw [← measureReal_def, hcompl, measureReal_compl hmeas, probReal_univ]
  rw [hP, Phi_neg]
  rw [abs_le]
  constructor <;> linarith
