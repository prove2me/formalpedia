-- Prove2me | solution 1 for CoVaRMC.Batching.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:48:22.651775+00:00
-- url     : https://prove2.me/submissions/6c7b07ba-8ef9-46db-87f9-874f3bf0c81d

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaREq6Aux



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

lemma measurable_fX (D : JointDensity) : Measurable D.fX := by
  have : StronglyMeasurable D.f := D.measurable.stronglyMeasurable
  exact (this.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

lemma measurable_condCDF (D : JointDensity) (y : ℝ) : Measurable (fun x => D.condCDF y x) := by
  unfold JointDensity.condCDF
  refine Measurable.div ?_ (measurable_fX D)
  have hm : Measurable (fun p : ℝ × ℝ => (Set.Iic y).indicator (fun v => D.f (p.1, v)) p.2) := by
    have : (fun p : ℝ × ℝ => (Set.Iic y).indicator (fun v => D.f (p.1, v)) p.2) =
        fun p => (Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2 * D.f p := by
      funext p
      by_cases h : p.2 ∈ Set.Iic y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [this]
    exact ((measurable_const.indicator measurableSet_Iic).comp measurable_snd).mul D.measurable
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have : (fun x => ∫ v in Set.Iic y, D.f (x, v)) =
      fun x => ∫ v, (Set.Iic y).indicator (fun v => D.f (x, v)) v := by
    funext x; rw [integral_indicator measurableSet_Iic]
  rw [this]
  exact h.measurable

/-- The defining property of the conditional distribution function. -/
lemma key (D : JointDensity) (g : ℝ → ℝ) (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) (y : ℝ) :
    ∫ p, g p.1 * (Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2 ∂D.law =
      ∫ p, g p.1 * D.condCDF y p.1 ∂D.law := by
  have hfm : Measurable (fun p => ENNReal.ofReal (D.f p)) := ENNReal.measurable_ofReal.comp D.measurable
  unfold JointDensity.law
  rw [integral_withDensity_eq_integral_toReal_smul hfm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hfm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (D.nonneg _), smul_eq_mul]
  have hfi : Integrable D.f (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact D.integrable
  have hcb : ∀ x, |D.condCDF y x| ≤ 1 := by
    intro x
    unfold JointDensity.condCDF
    have h0 : 0 ≤ ∫ v in Set.Iic y, D.f (x, v) := setIntegral_nonneg measurableSet_Iic fun _ _ => D.nonneg _
    have hX0 : 0 ≤ D.fX x := integral_nonneg fun _ => D.nonneg _
    by_cases hint : Integrable (fun v => D.f (x, v))
    · have hle : ∫ v in Set.Iic y, D.f (x, v) ≤ D.fX x :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => D.nonneg _)
      rw [abs_of_nonneg (div_nonneg h0 hX0)]
      rcases hX0.eq_or_lt with h | h
      · rw [← h, div_zero]; norm_num
      · exact (div_le_one h).mpr hle
    · have : D.fX x = 0 := integral_undef hint
      rw [this, div_zero]; norm_num
  rw [Measure.volume_eq_prod]
  have hint1 : Integrable (fun p : ℝ × ℝ => D.f p * (g p.1 * (Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2))
      (volume.prod volume) := by
    refine hfi.mul_bdd (c := 1) ?_ ?_
    · exact (hg.comp measurable_fst).mul
        ((measurable_const.indicator measurableSet_Iic).comp measurable_snd) |>.aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have : |(Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2| ≤ 1 := by
        by_cases h : p.2 ∈ Set.Iic y <;> simp [h]
      nlinarith [hgb p.1, abs_nonneg (g p.1), abs_nonneg ((Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2)]
  have hint2 : Integrable (fun p : ℝ × ℝ => D.f p * (g p.1 * D.condCDF y p.1)) (volume.prod volume) := by
    refine hfi.mul_bdd (c := 1) ?_ ?_
    · exact ((hg.comp measurable_fst).mul ((measurable_condCDF D y).comp measurable_fst)).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [hgb p.1, hcb p.1, abs_nonneg (g p.1), abs_nonneg (D.condCDF y p.1)]
  rw [integral_prod _ hint1, integral_prod _ hint2]
  apply integral_congr_ae
  filter_upwards [hfi.prod_right_ae] with x hx
  have e1 : ∫ w, D.f (x, w) * (g x * (Set.Iic y).indicator (fun _ => (1 : ℝ)) w) =
      g x * ∫ w in Set.Iic y, D.f (x, w) := by
    rw [← integral_const_mul, ← integral_indicator measurableSet_Iic]
    congr 1; funext w
    by_cases h : w ∈ Set.Iic y <;> simp [h, mul_comm]
  have e2 : ∫ w, D.f (x, w) * (g x * D.condCDF y x) = g x * (D.condCDF y x * D.fX x) := by
    rw [integral_mul_const]; unfold JointDensity.fX; ring
  rw [e1, e2]
  congr 1
  unfold JointDensity.condCDF
  by_cases hX : D.fX x = 0
  · rw [hX, mul_zero]
    have hz : (fun w => D.f (x, w)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => D.nonneg _) hx).mp hX
    rw [setIntegral_congr_ae measurableSet_Iic (hz.mono fun w hw _ => hw)]
    simp
  · rw [div_mul_cancel₀ _ hX]


lemma split (D : JointDensity) [IsProbabilityMeasure D.law] {n : ℕ} (j : Fin (n + 1))
    (H : (Fin (n + 1) → ℝ) → ℝ) (hH : Measurable H) (hHb : ∀ x, |H x| ≤ 1) (y : ℝ) :
    ∫ w, H (fun i => (w i).1) * (Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2
        ∂(Measure.pi fun _ => D.law) =
      ∫ w, H (fun i => (w i).1) * D.condCDF y (w j).1 ∂(Measure.pi fun _ => D.law) := by
  set μ := D.law
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) j
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j).symm
  have hxm : Measurable (fun w : Fin (n + 1) → ℝ × ℝ => fun i => (w i).1) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst
  have hind : ∀ a : ℝ, |(Set.Iic y).indicator (fun _ => (1 : ℝ)) a| ≤ 1 := by
    intro a; by_cases h : a ∈ Set.Iic y <;> simp [h]
  have hcb : ∀ x, |D.condCDF y x| ≤ 1 := by
    intro x
    unfold JointDensity.condCDF
    have h0 : 0 ≤ ∫ v in Set.Iic y, D.f (x, v) := setIntegral_nonneg measurableSet_Iic fun _ _ => D.nonneg _
    have hX0 : 0 ≤ D.fX x := integral_nonneg fun _ => D.nonneg _
    by_cases hint : Integrable (fun v => D.f (x, v))
    · have hle : ∫ v in Set.Iic y, D.f (x, v) ≤ D.fX x :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => D.nonneg _)
      rw [abs_of_nonneg (div_nonneg h0 hX0)]
      rcases hX0.eq_or_lt with h | h
      · rw [← h, div_zero]; norm_num
      · exact (div_le_one h).mpr hle
    · have : D.fX x = 0 := integral_undef hint
      rw [this, div_zero]; norm_num
  set F1 : (Fin (n + 1) → ℝ × ℝ) → ℝ :=
    fun w => H (fun i => (w i).1) * (Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2
  set F2 : (Fin (n + 1) → ℝ × ℝ) → ℝ := fun w => H (fun i => (w i).1) * D.condCDF y (w j).1
  have hF1m : Measurable F1 := (hH.comp hxm).mul
    ((measurable_const.indicator measurableSet_Iic).comp (measurable_pi_apply j).snd)
  have hF2m : Measurable F2 := (hH.comp hxm).mul
    ((measurable_condCDF D y).comp (measurable_pi_apply j).fst)
  have hint : ∀ F : (Fin (n + 1) → ℝ × ℝ) → ℝ, Measurable F → (∀ w, |F w| ≤ 1) →
      Integrable (fun z => F (e.symm z)) (μ.prod (Measure.pi fun _ => μ)) := by
    intro F hF hFb
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hF.comp e.symm.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]; exact hFb _
  have hF1b : ∀ w, |F1 w| ≤ 1 := fun w => by
    simp only [F1, abs_mul]
    nlinarith [hHb (fun i => (w i).1), hind (w j).2, abs_nonneg (H (fun i => (w i).1)),
      abs_nonneg ((Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2)]
  have hF2b : ∀ w, |F2 w| ≤ 1 := fun w => by
    simp only [F2, abs_mul]
    nlinarith [hHb (fun i => (w i).1), hcb (w j).1, abs_nonneg (H (fun i => (w i).1)),
      abs_nonneg (D.condCDF y (w j).1)]
  show ∫ w, F1 w ∂(Measure.pi fun _ => μ) = ∫ w, F2 w ∂(Measure.pi fun _ => μ)
  rw [← hmp.integral_comp' F1, ← hmp.integral_comp' F2,
    integral_prod_symm _ (hint F1 hF1m hF1b), integral_prod_symm _ (hint F2 hF2m hF2b)]
  congr 1
  funext w'
  set g : ℝ → ℝ := fun a => H (fun i => (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j ((a, 0) : ℝ × ℝ) w' i).1) with hgdef
  have hgx : ∀ p : ℝ × ℝ, H (fun i => (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j p w' i).1) = g p.1 := by
    intro p
    simp only [hgdef]
    congr 1
    funext i
    induction i using Fin.succAboveCases j with
    | x => simp [Fin.insertNth_apply_same]
    | p i => simp [Fin.insertNth_apply_succAbove]
  have hgm : Measurable g := by
    refine hH.comp (measurable_pi_lambda _ fun i => ?_)
    have : Measurable (fun a : ℝ => e.symm (((a, 0) : ℝ × ℝ), w')) :=
      e.symm.measurable.comp ((measurable_id.prodMk measurable_const).prodMk measurable_const)
    exact ((measurable_pi_apply i).comp this).fst
  have hgb : ∀ a, |g a| ≤ 1 := fun a => hHb _
  have h1 : ∀ p : ℝ × ℝ, F1 (e.symm (p, w')) = g p.1 * (Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2 := by
    intro p
    show H (fun i => (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j p w' i).1) *
      (Set.Iic y).indicator (fun _ => (1 : ℝ)) (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j p w' j).2 = _
    rw [hgx, Fin.insertNth_apply_same]
  have h2 : ∀ p : ℝ × ℝ, F2 (e.symm (p, w')) = g p.1 * D.condCDF y p.1 := by
    intro p
    show H (fun i => (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j p w' i).1) * D.condCDF y (Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ × ℝ) j p w' j).1 = _
    rw [hgx, Fin.insertNth_apply_same]
  simp_rw [h1, h2]
  exact key D g hgm hgb y

end CoVaREq6Aux

open CoVaREq6Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (m : ℕ) (hm : 0 < m) (y : ℝ) :
    pHat P S α m y = ∫ ω, D.condCDF y (Xorder S α m 0 ω) ∂P := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have : IsProbabilityMeasure D.law := by
    rw [← hSl (0, 0)]; exact Measure.isProbabilityMeasure_map (hSm _).aemeasurable
  set W : Ω → (Fin (n + 1) → ℝ × ℝ) := fun ω j => S (0, (j : ℕ)) ω with hWdef
  have hWm : Measurable W := measurable_pi_lambda _ fun j => hSm _
  have hind : iIndepFun (fun j : Fin (n + 1) => S (0, (j : ℕ))) P :=
    hSi.precomp (g := fun j : Fin (n + 1) => ((0 : ℕ), (j : ℕ)))
      (by intro a b h; simp only [Prod.mk.injEq, true_and] at h; exact Fin.ext h)
  have hlaw : P.map W = Measure.pi (fun _ => D.law) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun j => (hSm _).aemeasurable)).mp hind]
    congr 1; funext j; exact hSl _
  set r := rankIdx α (n + 1) hm with hrdef
  set J : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) := fun w => Tuple.sort (fun i => (w i).1) r with hJdef
  have hX : ∀ i : Fin (n + 1), Measurable (fun w : Fin (n + 1) → ℝ × ℝ => (w i).1) :=
    fun i => (measurable_pi_apply i).fst
  have hY : ∀ i : Fin (n + 1), Measurable (fun w : Fin (n + 1) → ℝ × ℝ => (w i).2) :=
    fun i => (measurable_pi_apply i).snd
  set G1 : (Fin (n + 1) → ℝ × ℝ) → ℝ :=
    fun w => (Set.Iic y).indicator (fun _ => (1 : ℝ)) (w (J w)).2 with hG1def
  set G2 : (Fin (n + 1) → ℝ × ℝ) → ℝ := fun w => D.condCDF y (w (J w)).1 with hG2def
  have hG1m : Measurable G1 :=
    (measurable_const.indicator measurableSet_Iic).comp
      (measurable_induced (fun i (w : Fin (n + 1) → ℝ × ℝ) => (w i).1)
        (fun i (w : Fin (n + 1) → ℝ × ℝ) => (w i).2) hX hY r)
  have hG2m : Measurable G2 :=
    (measurable_condCDF D y).comp (measurable_induced (fun i (w : Fin (n + 1) → ℝ × ℝ) => (w i).1)
      (fun i (w : Fin (n + 1) → ℝ × ℝ) => (w i).1) hX hX r)
  have e1 : pHat P S α (n + 1) y = ∫ ω, G1 (W ω) ∂P := by
    have hset : MeasurableSet {ω | Yhat S α (n + 1) 0 ω ≤ y} :=
      measurableSet_le (measurable_Yhat S hSm α (n + 1) 0) measurable_const
    have : (fun ω => G1 (W ω)) = {ω | Yhat S α (n + 1) 0 ω ≤ y}.indicator 1 := by
      funext ω
      have hY0 : Yhat S α (n + 1) 0 ω = (W ω (J (W ω))).2 := by
        simp only [Yhat, dif_pos hm, ImpactInvesting.Portfolio.inducedOrderStat]; rfl
      by_cases h : Yhat S α (n + 1) 0 ω ≤ y
      · rw [Set.indicator_of_mem (show ω ∈ {ω | Yhat S α (n + 1) 0 ω ≤ y} from h)]
        simp only [hG1def]
        rw [Set.indicator_of_mem (show (W ω (J (W ω))).2 ∈ Set.Iic y by rw [← hY0]; exact h)]
        rfl
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | Yhat S α (n + 1) 0 ω ≤ y} from h)]
        simp only [hG1def]
        rw [Set.indicator_of_notMem (show (W ω (J (W ω))).2 ∉ Set.Iic y by
          rw [← hY0]; exact h)]
    rw [this, integral_indicator_one hset]
    rfl
  have e2 : ∫ ω, D.condCDF y (Xorder S α (n + 1) 0 ω) ∂P = ∫ ω, G2 (W ω) ∂P := by
    congr 1
  rw [e1, e2, ← integral_map hWm.aemeasurable hG1m.aestronglyMeasurable,
    ← integral_map hWm.aemeasurable hG2m.aestronglyMeasurable, hlaw]
  -- decompose according to the value of `J`
  obtain ⟨H, hHdef⟩ : ∃ H : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ,
      H = fun j x => if Tuple.sort x r = j then 1 else 0 := ⟨_, rfl⟩
  have hHm : ∀ j, Measurable (H j) := by
    intro j
    have hs : MeasurableSet {x : Fin (n + 1) → ℝ | Tuple.sort x r = j} := by
      have : {x : Fin (n + 1) → ℝ | Tuple.sort x r = j} =
          ⋃ σ ∈ {σ : Equiv.Perm (Fin (n + 1)) | σ r = j}, {x | Tuple.sort (fun i => x i) = σ} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
        exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨σ, h1, h2⟩ => by rw [h2]; exact h1⟩
      rw [this]
      refine MeasurableSet.biUnion (Set.to_countable _) fun σ _ => ?_
      have h := measurableSet_sort_eq (Ω := Fin (n + 1) → ℝ) (fun i x => x i)
        (fun i => measurable_pi_apply i) σ
      exact h
    rw [hHdef]
    exact Measurable.ite hs measurable_const measurable_const
  have hHb : ∀ j x, |H j x| ≤ 1 := by
    intro j x; simp only [hHdef]; split_ifs <;> norm_num
  have hG1sum : G1 = fun w => ∑ j, H j (fun i => (w i).1) *
      (Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2 := by
    funext w
    rw [Finset.sum_eq_single (J w)]
    · simp [hHdef, hG1def, hJdef]
    · intro b _ hb
      simp only [hHdef]
      rw [if_neg (fun h => hb (h.symm)), zero_mul]
    · simp
  have hG2sum : G2 = fun w => ∑ j, H j (fun i => (w i).1) * D.condCDF y (w j).1 := by
    funext w
    rw [Finset.sum_eq_single (J w)]
    · simp [hHdef, hG2def, hJdef]
    · intro b _ hb
      simp only [hHdef]
      rw [if_neg (fun h => hb (h.symm)), zero_mul]
    · simp
  have hxm : Measurable (fun w : Fin (n + 1) → ℝ × ℝ => fun i => (w i).1) :=
    measurable_pi_lambda _ hX
  have hcb : ∀ x, |D.condCDF y x| ≤ 1 := by
    intro x
    unfold JointDensity.condCDF
    have h0 : 0 ≤ ∫ v in Set.Iic y, D.f (x, v) := setIntegral_nonneg measurableSet_Iic fun _ _ => D.nonneg _
    have hX0 : 0 ≤ D.fX x := integral_nonneg fun _ => D.nonneg _
    by_cases hint : Integrable (fun v => D.f (x, v))
    · have hle : ∫ v in Set.Iic y, D.f (x, v) ≤ D.fX x :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => D.nonneg _)
      rw [abs_of_nonneg (div_nonneg h0 hX0)]
      rcases hX0.eq_or_lt with h | h
      · rw [← h, div_zero]; norm_num
      · exact (div_le_one h).mpr hle
    · have : D.fX x = 0 := integral_undef hint
      rw [this, div_zero]; norm_num
  rw [hG1sum, hG2sum, integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    exact split D j (H j) (hHm j) (hHb j) y
  · intro j _
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((hHm j).comp hxm).mul ((measurable_condCDF D y).comp (hX j))).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hHb j (fun i => (w i).1), hcb (w j).1, abs_nonneg (H j (fun i => (w i).1)),
      abs_nonneg (D.condCDF y (w j).1)]
  · intro j _
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((hHm j).comp hxm).mul ((measurable_const.indicator measurableSet_Iic).comp (hY j))).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have : |(Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2| ≤ 1 := by
      by_cases h : (w j).2 ∈ Set.Iic y <;> simp [h]
    nlinarith [hHb j (fun i => (w i).1), abs_nonneg (H j (fun i => (w i).1)),
      abs_nonneg ((Set.Iic y).indicator (fun _ => (1 : ℝ)) (w j).2)]
