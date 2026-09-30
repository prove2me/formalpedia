-- Prove2me | solution 1 for BanditAlgorithm.exp3ix_estimate_concentration_variance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:47.977045+00:00
-- url     : https://prove2.me/submissions/78ccfa3d-9691-4067-8282-6f4ce61b4240

import Mathlib
import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Exp3Concentration

open BanditAlgorithm

lemma exp_discount {z l : ℝ} (hz : 0 ≤ z) (h : z ≤ 2 * l) :
    Real.exp (z / (1 + l)) ≤ 1 + z := by
  have hl : 0 ≤ l := by linarith
  apply (Real.le_log_iff_exp_le (by positivity)).mp
  apply le_trans _ (Real.le_log_one_add_of_nonneg hz)
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + l)
    (by positivity : 0 < z + 2)).mpr
  nlinarith [mul_nonneg hz (sub_nonneg.mpr h)]

lemma prob_pos {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : 0 < exp3IXProb η γ m h i := by
  unfold exp3IXProb expWeights
  exact div_pos (Real.exp_pos _) (Finset.sum_pos'
    (fun _ _ => (Real.exp_pos _).le) ⟨i, Finset.mem_univ _, Real.exp_pos _⟩)

lemma prob_sum {k : ℕ} (hk : 0 < k) (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) : ∑ i, exp3IXProb η γ m h i = 1 := by
  unfold exp3IXProb expWeights
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨⟨0, hk⟩, Finset.mem_univ _, Real.exp_pos _⟩))

lemma estimate_measurable {k : ℕ} (η γ : ℝ) :
    ∀ (m : ℕ) (i : Fin k),
      Measurable (fun h : BanditHistory k m => exp3IXEstimate η γ m h i) := by
  classical
  intro m
  induction m with
  | zero => intro i; simp [exp3IXEstimate]
  | succ m ih =>
    intro i
    have hinit : Measurable (fun h : BanditHistory k (m + 1) => Fin.init h) := by
      exact measurable_pi_iff.mpr fun t => measurable_pi_apply t.castSucc
    have hp : Measurable (fun h : BanditHistory k (m + 1) =>
        exp3IXProb η γ m (Fin.init h) i) := by
      unfold exp3IXProb expWeights
      apply Measurable.div
      · exact ((measurable_const.mul ((ih i).comp hinit)).neg).exp
      · exact Finset.measurable_sum _ fun j _ =>
          ((measurable_const.mul ((ih j).comp hinit)).neg).exp
    have hlast : Measurable (fun h : BanditHistory k (m + 1) => h (Fin.last m)) :=
      measurable_pi_apply (Fin.last m)
    have hset : MeasurableSet {h : BanditHistory k (m + 1) |
        (h (Fin.last m)).1 = i} :=
      (measurableSet_singleton i).preimage (measurable_fst.comp hlast)
    have hinc : Measurable (fun h : BanditHistory k (m + 1) =>
        if (h (Fin.last m)).1 = i then
          (1 - (h (Fin.last m)).2) / (exp3IXProb η γ m (Fin.init h) i + γ) else 0) :=
      Measurable.ite hset
        ((measurable_const.sub (measurable_snd.comp hlast)).div
          (hp.add_const γ)) measurable_const
    simpa only [exp3IXEstimate, exp3IXProb, Pi.add_def, Function.comp_def] using
      ((ih i).comp hinit).add hinc

noncomputable def deviation {k : ℕ} (x : ℕ → Fin k → ℝ) (η : ℝ)
    (a : Fin k → ℝ) (m : ℕ) (h : BanditHistory k m) : ℝ :=
  ∑ i, a i * (exp3IXEstimate η (η / 2) m h i - ∑ t : Fin m, (1 - x t i))

lemma deviation_measurable {k : ℕ} (x : ℕ → Fin k → ℝ) (η : ℝ)
    (a : Fin k → ℝ) (m : ℕ) : Measurable (deviation x η a m) := by
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul
    ((estimate_measurable η (η / 2) m i).sub_const _)

lemma deviation_snoc {k : ℕ} (x : ℕ → Fin k → ℝ) (η : ℝ)
    (a : Fin k → ℝ) (m : ℕ) (h : BanditHistory k m) (j : Fin k) :
    deviation x η a (m + 1) (Fin.snoc h (j, x m j)) =
      deviation x η a m h + a j * (1 - x m j) /
        (exp3IXProb η (η / 2) m h j + η / 2) - ∑ i, a i * (1 - x m i) := by
  classical
  unfold deviation
  simp only [exp3IXEstimate, Fin.init_snoc, Fin.snoc_last,
    Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  change (∑ i, a i * (exp3IXEstimate η (η / 2) m h i +
    (if j = i then (1 - x m j) / (exp3IXProb η (η / 2) m h i + η / 2) else 0) -
      ((∑ t : Fin m, (1 - x t i)) + (1 - x m i)))) = _
  simp_rw [show ∀ i : Fin k,
      a i * (exp3IXEstimate η (η / 2) m h i +
        (if j = i then (1 - x m j) / (exp3IXProb η (η / 2) m h i + η / 2) else 0) -
        ((∑ t : Fin m, (1 - x t i)) + (1 - x m i))) =
      a i * (exp3IXEstimate η (η / 2) m h i - ∑ t : Fin m, (1 - x t i)) +
        (if j = i then a j * (1 - x m j) /
          (exp3IXProb η (η / 2) m h j + η / 2) else 0) - a i * (1 - x m i) from by
    intro i; split_ifs with hij <;> (try subst i) <;> ring]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma scalar_step {k : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (a y p : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 η)
    (hy : ∀ i, y i ∈ Set.Icc 0 1) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    (∑ j, p j * Real.exp (a j * y j / (p j + η / 2) - ∑ i, a i * y i)) ≤ 1 := by
  have hpoint : ∀ j, Real.exp (a j * y j / (p j + η / 2)) ≤
      1 + a j * y j / p j := by
    intro j
    have hay : a j * y j ≤ η :=
      (mul_le_mul_of_nonneg_left (hy j).2 (ha j).1).trans (by simpa using (ha j).2)
    have hbound : a j * y j / p j ≤ 2 * ((η / 2) / p j) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right (hp j)).mpr
      linarith
    have h := exp_discount (div_nonneg (mul_nonneg (ha j).1 (hy j).1) (hp j).le) hbound
    convert h using 2 <;> field_simp [ne_of_gt (hp j)]
  calc
    (∑ j, p j * Real.exp (a j * y j / (p j + η / 2) - ∑ i, a i * y i)) =
        (∑ j, p j * Real.exp (a j * y j / (p j + η / 2))) /
          Real.exp (∑ i, a i * y i) := by
      simp only [Real.exp_sub, mul_div_assoc, Finset.sum_div]
    _ ≤ (∑ j, (p j + a j * y j)) / Real.exp (∑ i, a i * y i) := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
      apply Finset.sum_le_sum
      intro j _
      calc
        p j * Real.exp (a j * y j / (p j + η / 2)) ≤
            p j * (1 + a j * y j / p j) := mul_le_mul_of_nonneg_left (hpoint j) (hp j).le
        _ = p j + a j * y j := by field_simp [ne_of_gt (hp j)]
    _ ≤ 1 := by
      rw [Finset.sum_add_distrib, hs, div_le_one (Real.exp_pos _)]
      linarith [Real.add_one_le_exp (∑ i, a i * y i)]

end Exp3Concentration

namespace Exp3Concentration

open BanditAlgorithm

lemma potential_step {k : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 η)
    (m : ℕ) (h : BanditHistory k m) :
    (∑ j, exp3IXProb η (η / 2) m h j *
      Real.exp (deviation x η a (m + 1) (Fin.snoc h (j, x m j)))) ≤
        Real.exp (deviation x η a m h) := by
  have hstep := scalar_step hk η hη a (fun i => 1 - x m i)
    (exp3IXProb η (η / 2) m h) ha
    (fun i => ⟨sub_nonneg.mpr (hx m i).2, by linarith [(hx m i).1]⟩)
    (prob_pos η (η / 2) m h) (prob_sum hk η (η / 2) m h)
  calc
    _ = Real.exp (deviation x η a m h) *
        (∑ j, exp3IXProb η (η / 2) m h j *
          Real.exp (a j * (1 - x m j) / (exp3IXProb η (η / 2) m h j + η / 2) -
            ∑ i, a i * (1 - x m i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [deviation_snoc, show deviation x η a m h +
          a j * (1 - x m j) / (exp3IXProb η (η / 2) m h j + η / 2) -
          ∑ i, a i * (1 - x m i) = deviation x η a m h +
          (a j * (1 - x m j) / (exp3IXProb η (η / 2) m h j + η / 2) -
            ∑ i, a i * (1 - x m i)) by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (deviation x η a m h) * 1 :=
      mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = _ := mul_one _

lemma lintegral_step {k : ℕ} (x : ℕ → Fin k → ℝ) (η : ℝ)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π)
    (m : ℕ) (h : BanditHistory k m)
    (f : BanditHistory k (m + 1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (Fin.snoc h z) ∂(adversarialStepKernel x π m h)) =
      ∑ j, ENNReal.ofReal (exp3IXProb η (η / 2) m h j) *
        f (Fin.snoc h (j, x m j)) := by
  classical
  have hsnoc : Measurable (fun z : Fin k × ℝ => Fin.snoc (α := fun _ => Fin k × ℝ) h z) := by
    simpa only [Function.comp_def, id_eq] using measurable_banditHistorySnoc.comp
      ((measurable_const : Measurable (fun _ : Fin k × ℝ => h)).prodMk measurable_id)
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    lintegral_map (show Measurable (fun z : Fin k × ℝ => f (Fin.snoc h z)) from by
      simpa only [Function.comp_def] using hf.comp hsnoc) (measurable_of_countable _), hπ m h,
    lintegral_finset_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

lemma potential_lintegral_le_one {k : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π)
    (a : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 η) (n : ℕ) :
    (∫⁻ h, ENNReal.ofReal (Real.exp (deviation x η a n h))
      ∂(adversarialMeasure x π n)) ≤ 1 := by
  induction n with
  | zero => simp [adversarialMeasure, deviation, exp3IXEstimate]
  | succ n ih =>
    have hf := (deviation_measurable x η a (n + 1)).exp.ennreal_ofReal
    rw [adversarialMeasure, lintegral_map hf measurable_banditHistorySnoc]
    rw [Measure.lintegral_compProd (show Measurable (fun p : BanditHistory k n × (Fin k × ℝ) =>
      ENNReal.ofReal (Real.exp (deviation x η a (n + 1) (Fin.snoc p.1 p.2)))) from by
        simpa only [Function.comp_def] using hf.comp measurable_banditHistorySnoc)]
    apply le_trans (lintegral_mono fun h => ?_) ih
    rw [lintegral_step x η π hπ n h _ hf]
    simp_rw [← ENNReal.ofReal_mul (prob_pos η (η / 2) n h _).le]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (prob_pos η (η / 2) n h i).le (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (potential_step hk η hη x hx a ha n h)

lemma reward_support_measurable {k n : ℕ} :
    MeasurableSet {h : BanditHistory k n | ∀ t, (h t).2 ∈ Set.Icc (0 : ℝ) 1} := by
  have hi : ∀ t : Fin n, MeasurableSet
      {h : BanditHistory k n | (h t).2 ∈ Set.Icc (0 : ℝ) 1} := fun t =>
    measurableSet_Icc.preimage (measurable_snd.comp (measurable_pi_apply t))
  simpa only [Set.setOf_forall] using MeasurableSet.iInter hi

lemma reward_support {k : ℕ} (x : ℕ → Fin k → ℝ)
    (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1) (π : BanditPolicy k) (n : ℕ) :
    ∀ᵐ h ∂(adversarialMeasure x π n), ∀ t, (h t).2 ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun h t => Fin.elim0 t
  | succ n ih =>
    rw [adversarialMeasure]
    apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
      reward_support_measurable).mpr
    apply Measure.ae_compProd_of_ae_ae
      (reward_support_measurable.preimage measurable_banditHistorySnoc)
    filter_upwards [ih] with h hh
    rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
    apply (ae_map_iff (measurable_of_countable _).aemeasurable
      (reward_support_measurable.preimage
        (measurable_banditHistorySnoc.comp (measurable_const.prodMk measurable_id)))).mpr
    exact Filter.Eventually.of_forall fun j t => by
      refine Fin.lastCases ?_ (fun s => ?_) t
      · simpa using hx n j
      · simpa using hh s

lemma weighted_tail {k : ℕ} (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t i, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (hπ : IsExp3IXPolicy η (η / 2) π)
    (a : Fin k → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 η) (n : ℕ)
    (d : ℝ) (hd : 0 < d) :
    adversarialMeasure x π n {h | Real.log (1 / d) ≤ deviation x η a n h} ≤
      ENNReal.ofReal d := by
  let f := fun h : BanditHistory k n => ENNReal.ofReal (Real.exp (deviation x η a n h))
  have hf : Measurable f := (deviation_measurable x η a n).exp.ennreal_ofReal
  have hmark := meas_ge_le_lintegral_div (μ := adversarialMeasure x π n) hf.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hd))) ENNReal.ofReal_ne_top
  calc
    _ ≤ adversarialMeasure x π n {h | ENNReal.ofReal (1 / d) ≤ f h} := by
      apply measure_mono
      intro h hh
      exact ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp (one_div_pos.mpr hd)).mp hh)
    _ ≤ (∫⁻ h, f h ∂adversarialMeasure x π n) / ENNReal.ofReal (1 / d) := hmark
    _ ≤ 1 / ENNReal.ofReal (1 / d) := by
      exact ENNReal.div_le_div_right (potential_lintegral_le_one hk η hη x hx π hπ a ha n) _
    _ = ENNReal.ofReal d := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (one_div_pos.mpr hd)]
      simp

end Exp3Concentration

open BanditAlgorithm Exp3Concentration

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        (∃ t : Fin n, (h t).2 ∉ Set.Icc (0 : ℝ) 1) ∨
        Real.log ((k + 1) / δ) / η ≤
          (⨆ i : Fin k,
            BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i)) ∨
        Real.log ((k + 1) / δ) / η ≤
          ∑ i : Fin k,
            (BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i))} ≤
      ENNReal.ofReal δ := by
  classical
  have hk0 : 0 < k := by omega
  letI : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  let μ := adversarialMeasure x π n
  let d : ℝ := δ / ((k : ℝ) + 1)
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have hd : 0 < d := div_pos hδ.1 hk1
  have hdiv : 1 / d = ((k : ℝ) + 1) / δ := by dsimp [d]; field_simp
  let B : ℝ := Real.log (((k : ℝ) + 1) / δ) / η
  let R := fun (h : BanditHistory k n) (i : Fin k) =>
    exp3IXEstimate η (η / 2) n h i - ∑ t : Fin n, (1 - x t i)
  have hsingle : ∀ i : Fin k, μ {h | B ≤ R h i} ≤ ENNReal.ofReal d := by
    intro i
    have hw := weighted_tail hk0 η hη x hx π hπ (fun j => if j = i then η else 0)
      (fun j => by by_cases hj : j = i <;> simp [hj, hη.le]) n d hd
    apply (measure_mono (fun h hh => ?_)).trans hw
    change Real.log (1 / d) ≤ deviation x η (fun j => if j = i then η else 0) n h
    simp only [deviation, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hdiv]
    exact (div_le_iff₀ hη).mp hh |>.trans_eq (mul_comm _ _)
  have hall : μ {h | B ≤ ∑ i, R h i} ≤ ENNReal.ofReal d := by
    have hw := weighted_tail hk0 η hη x hx π hπ (fun _ => η)
      (fun _ => ⟨hη.le, le_rfl⟩) n d hd
    apply (measure_mono (fun h hh => ?_)).trans hw
    change Real.log (1 / d) ≤ deviation x η (fun _ => η) n h
    rw [hdiv]
    dsimp [deviation]
    rw [← Finset.mul_sum]
    exact (div_le_iff₀ hη).mp hh |>.trans_eq (mul_comm _ _)
  have hmaximum : μ {h | B ≤ ⨆ i, R h i} ≤ (k : ℝ≥0∞) * ENNReal.ofReal d := by
    calc
      _ ≤ μ (⋃ i : Fin k, {h | B ≤ R h i}) := by
        apply measure_mono
        intro h hh
        obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := R h)
        apply Set.mem_iUnion.mpr
        refine ⟨i, ?_⟩
        change B ≤ R h i
        rw [hi]
        exact hh
      _ ≤ ∑ i : Fin k, μ {h | B ≤ R h i} := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : Fin k, ENNReal.ofReal d := Finset.sum_le_sum fun i _ => hsingle i
      _ = _ := by simp
  have hbadzero : μ {h : BanditHistory k n | ∃ t, (h t).2 ∉ Set.Icc (0 : ℝ) 1} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [reward_support x hx π n] with h hh
    simpa using hh
  change μ {h | (∃ t, (h t).2 ∉ Set.Icc (0 : ℝ) 1) ∨
    B ≤ ⨆ i, R h i ∨ B ≤ ∑ i, R h i} ≤ ENNReal.ofReal δ
  simp only [Set.setOf_or]
  calc
    _ ≤ μ {h : BanditHistory k n | ∃ t, (h t).2 ∉ Set.Icc (0 : ℝ) 1} +
        (μ {h | B ≤ ⨆ i, R h i} + μ {h | B ≤ ∑ i, R h i}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ 0 + ((k : ℝ≥0∞) * ENNReal.ofReal d + ENNReal.ofReal d) :=
      add_le_add (le_of_eq hbadzero) (add_le_add hmaximum hall)
    _ = ENNReal.ofReal δ := by
      rw [zero_add, ← add_one_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ← ENNReal.ofReal_mul hk1.le]
      congr 1
      dsimp [d]
      field_simp
