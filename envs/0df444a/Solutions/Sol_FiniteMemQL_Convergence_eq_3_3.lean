-- Prove2me | solution 1 for FiniteMemQL.Convergence.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:46:00.943123+00:00
-- url     : https://prove2.me/submissions/d1158150-30fe-40b2-9d00-685018ccd220

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Aux_FMQ_eq33

open FiniteMemQL.Convergence
open scoped ENNReal

lemma inf_diff {U : Type*} [Fintype U] [Nonempty U] (f g : U → ℝ) (d : ℝ)
    (h : ∀ v, |f v - g v| ≤ d) : |(⨅ v, f v) - ⨅ v, g v| ≤ d := by
  rw [abs_le]
  constructor
  · have : (⨅ v, g v) - d ≤ ⨅ v, f v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range g) v, (abs_le.mp (h v)).1]
    linarith
  · have : (⨅ v, f v) - d ≤ ⨅ v, g v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range f) v, (abs_le.mp (h v)).2]
    linarith

lemma inf_lip {U : Type*} [Fintype U] [Nonempty U] :
    Continuous (fun f : U → ℝ => ⨅ v : U, f v) := by
  have : LipschitzWith 1 (fun f : U → ℝ => ⨅ v : U, f v) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact inf_diff _ _ _ fun v => by rw [← Real.dist_eq]; exact dist_le_pi_dist f g v
  exact this.continuous

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

lemma normalize_univ_le (μ : Measure X) : FiniteMemQL.Convergence.normalize μ Set.univ ≤ 1 := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [h0, mul_zero]; exact zero_le_one
  rcases eq_or_ne (μ Set.univ) ⊤ with ht | ht
  · rw [ht]; simp
  · rw [ENNReal.inv_mul_cancel h0 ht]

lemma predict_univ (M : POMDP X Y U) (μ : Measure X) (u : U) :
    predict M μ u Set.univ = μ Set.univ := by
  unfold predict
  have hm : Measurable (fun x => M.T (x, u)) :=
    M.T.measurable.comp (measurable_id.prodMk measurable_const)
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

lemma sum_correct [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) (ν : Measure X) :
    ∑ y : Y, correct M ν y Set.univ = ν Set.univ := by
  unfold correct
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← lintegral_finset_sum _ (fun y _ => M.O.measurable_coe (measurableSet_singleton y))]
  have : ∀ x, ∑ y : Y, M.O x {y} = 1 := by
    intro x
    rw [sum_measure_singleton]
    simp
  simp only [this, lintegral_const, one_mul]

lemma correct_univ_le [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U)
    (ν : Measure X) (y : Y) : correct M ν y Set.univ ≤ ν Set.univ := by
  rw [← sum_correct M ν]
  exact Finset.single_le_sum (f := fun y => correct M ν y Set.univ) (fun _ _ => zero_le)
    (Finset.mem_univ y)

lemma correct_smul (M : POMDP X Y U) (c : ℝ≥0∞) (μ : Measure X) (y : Y) :
    correct M (c • μ) y = c • correct M μ y := by
  unfold correct; exact withDensity_smul_measure c _

lemma predict_smul (M : POMDP X Y U) (c : ℝ≥0∞) (μ : Measure X) (u : U) :
    predict M (c • μ) u = c • predict M μ u := by
  unfold predict; exact Measure.bind_smul c μ _

lemma unnormPost_smul (M : POMDP X Y U) (N : ℕ) :
    ∀ (c : ℝ≥0∞) (π : Measure X) (I : Window Y U N),
      unnormPost M N (c • π) I = c • unnormPost M N π I := by
  induction N with
  | zero => intro c π I; exact correct_smul M c π _
  | succ N ih =>
    intro c π I
    simp only [unnormPost]
    rw [correct_smul, predict_smul, ih]

lemma normalize_smul (μ : Measure X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hμ : μ Set.univ ≠ ⊤) : FiniteMemQL.Convergence.normalize (c • μ) =
      FiniteMemQL.Convergence.normalize μ := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul, smul_smul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [Measure.measure_univ_eq_zero.1 h0]; simp
  · congr 1
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hc0 hct, mul_one]

lemma eq_smul_normalize (μ : Measure X) (hμ : μ Set.univ ≠ ⊤) :
    μ = μ Set.univ • FiniteMemQL.Convergence.normalize μ := by
  unfold FiniteMemQL.Convergence.normalize
  rw [smul_smul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [Measure.measure_univ_eq_zero.1 h0]; simp
  · rw [ENNReal.mul_inv_cancel h0 hμ, one_smul]

lemma tail_snoc' {α : Type*} {n : ℕ} (p : Fin (n + 1) → α) (x : α) :
    Fin.tail (Fin.snoc (α := fun _ => α) p x) = Fin.snoc (α := fun _ => α) (Fin.tail p) x := by
  conv_lhs => rw [← Fin.cons_self_tail p]
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons]

lemma unnormPost_snoc (M : POMDP X Y U) (N : ℕ) :
    ∀ (π : Measure X) (ys : Fin (N + 1) → Y) (us : Fin N → U) (u : U) (y : Y),
      unnormPost M (N + 1) π (Fin.snoc (α := fun _ => Y) ys y, Fin.snoc (α := fun _ => U) us u) =
        correct M (predict M (unnormPost M N π (ys, us)) u) y := by
  induction N with
  | zero =>
    intro π ys us u y
    simp only [unnormPost]
    congr 2
  | succ N ih =>
    intro π ys us u y
    rw [unnormPost]
    simp only
    rw [tail_snoc', tail_snoc', ih]
    simp only [unnormPost]
    rw [Fin.snoc_apply_zero, Fin.snoc_apply_zero]

lemma unnormPost_univ_le [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) (N : ℕ) :
    ∀ (π : Measure X) (I : Window Y U N), unnormPost M N π I Set.univ ≤ π Set.univ := by
  induction N with
  | zero => intro π I; exact correct_univ_le M π _
  | succ N ih =>
    intro π I
    simp only [unnormPost]
    refine (ih _ _).trans ?_
    rw [predict_univ]
    exact correct_univ_le M π _

/-- Bayes consistency of the window posterior with the filter update. -/
lemma post_nextPrior [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U) {N : ℕ}
    (π : Measure X) [IsFiniteMeasure π] (I : Window Y U N) (u : U) (y : Y)
    (hc : correct M π (I.1 0) Set.univ ≠ 0) :
    post M (nextPrior M π I u) (shift I u y) = filterUpdate M (post M π I) u y := by
  set a := correct M π (I.1 0) with ha
  have hat : a Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top π _) (correct_univ_le M π _)
  have hm : unnormPost M N π I Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top π _) (unnormPost_univ_le M N π I)
  have e1 : unnormPost M N (nextPrior M π I u) (shift I u y) =
      (a Set.univ)⁻¹ • correct M (predict M (unnormPost M N π I) u) y := by
    unfold nextPrior FiniteMemQL.Convergence.normalize
    rw [predict_smul, unnormPost_smul, ← ha]
    congr 1
    rw [← unnormPost_snoc]
    simp only [unnormPost, shift]
    simp only [Fin.snoc_apply_zero, ha]
  unfold post filterUpdate
  rw [e1]
  have hfin : correct M (predict M (unnormPost M N π I) u) y Set.univ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hm ?_
    exact (correct_univ_le M _ y).trans (predict_univ M _ u).le
  rw [normalize_smul _ _ (ENNReal.inv_ne_zero.2 hat) (ENNReal.inv_ne_top.2 hc) hfin]
  -- normalize (correct (predict m)) = normalize (correct (predict (normalize m)))
  conv_lhs => rw [eq_smul_normalize (unnormPost M N π I) hm]
  rw [predict_smul, correct_smul]
  rcases eq_or_ne (unnormPost M N π I Set.univ) 0 with h0 | h0
  · rw [h0, zero_smul]
    have : FiniteMemQL.Convergence.normalize (unnormPost M N π I) = 0 := by
      unfold FiniteMemQL.Convergence.normalize
      rw [Measure.measure_univ_eq_zero.1 h0, smul_zero]
    rw [this]
    unfold FiniteMemQL.Convergence.normalize
    simp [predict, correct]
  · have hfin2 : correct M (predict M (FiniteMemQL.Convergence.normalize
        (unnormPost M N π I)) u) y Set.univ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      exact (correct_univ_le M _ y).trans ((predict_univ M _ u).le.trans (normalize_univ_le _))
    rw [normalize_smul _ _ h0 hm hfin2]

lemma unnormPost_univ_le_correct [Fintype Y] [MeasurableSingletonClass Y] (M : POMDP X Y U)
    (N : ℕ) (π : Measure X) (I : Window Y U N) :
    unnormPost M N π I Set.univ ≤ correct M π (I.1 0) Set.univ := by
  cases N with
  | zero => exact le_rfl
  | succ N =>
    simp only [unnormPost]
    refine (unnormPost_univ_le M N _ _).trans ?_
    rw [predict_univ]

section JS

variable [Fintype Y] [Fintype U] [Nonempty U] [MeasurableSingletonClass Y]

lemma sum_obsProb_le (M : POMDP X Y U) (z : Measure X) (hz : z Set.univ ≤ 1) (u : U) :
    ∑ y : Y, obsProb M z u y ≤ 1 := by
  set ν := predict M z u with hν
  have hνle : ν Set.univ ≤ 1 := by rw [hν, predict_univ]; exact hz
  have hfin : ∀ y, correct M ν y Set.univ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((correct_univ_le M ν y).trans hνle)
  have : ∑ y : Y, obsProb M z u y = (∑ y : Y, correct M ν y Set.univ).toReal := by
    rw [ENNReal.toReal_sum (fun y _ => hfin y)]
    rfl
  rw [this, sum_correct]
  calc (ν Set.univ).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hνle
    _ = 1 := ENNReal.toReal_one

lemma beliefCost_bdd (M : POMDP X Y U) (B : ℝ) (hB : ∀ x u, |M.c x u| ≤ B) (hB0 : 0 ≤ B)
    (z : Measure X) (hz : z Set.univ ≤ 1) (u : U) : |beliefCost M z u| ≤ B := by
  haveI : IsFiniteMeasure z := ⟨lt_of_le_of_lt hz ENNReal.one_lt_top⟩
  unfold beliefCost
  have h := norm_integral_le_of_norm_le_const (μ := z) (f := fun x => M.c x u) (C := B)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x u)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have : z.real Set.univ ≤ 1 := by
    unfold Measure.real
    calc (z Set.univ).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hz
      _ = 1 := ENNReal.toReal_one
  have h0 : 0 ≤ z.real Set.univ := measureReal_nonneg
  nlinarith

lemma bellman_lip (M : POMDP X Y U) (V W : Measure X → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ F : Measure X, F Set.univ ≤ 1 → |V F - W F| ≤ d) (z : Measure X)
    (hz : z Set.univ ≤ 1) : |beliefBellman M V z - beliefBellman M W z| ≤ M.β * d := by
  have hβ0 := M.β_pos
  unfold beliefBellman
  apply inf_diff
  intro u
  rw [add_sub_add_left_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hβ0]
  apply mul_le_mul_of_nonneg_left _ hβ0.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y : Y, |obsProb M z u y * V (filterUpdate M z u y)
        - obsProb M z u y * W (filterUpdate M z u y)|
      ≤ ∑ y : Y, obsProb M z u y * d := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ obsProb M z u y from
          ENNReal.toReal_nonneg)]
        exact mul_le_mul_of_nonneg_left (h _ (normalize_univ_le _)) ENNReal.toReal_nonneg
    _ = (∑ y : Y, obsProb M z u y) * d := by rw [Finset.sum_mul]
    _ ≤ 1 * d := mul_le_mul_of_nonneg_right (sum_obsProb_le M z hz u) hd
    _ = d := one_mul _

/-- `J*_β` is a fixed point of the belief Bellman operator at every sub-probability measure. -/
lemma jstar_fix (M : POMDP X Y U) (z : Measure X) (hz : z Set.univ ≤ 1) :
    Jstar M z = beliefBellman M (Jstar M) z := by
  obtain ⟨B0, hB0⟩ := M.c_bdd
  set B := max B0 0 with hBdef
  have hB : ∀ x u, |M.c x u| ≤ B := fun x u => (hB0 x u).trans (le_max_left _ _)
  have hBnn : 0 ≤ B := le_max_right _ _
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  set V : ℕ → Measure X → ℝ := fun n => (beliefBellman M)^[n] 0 with hVdef
  have hFU : ∀ z u y, filterUpdate M z u y Set.univ ≤ 1 := fun _ _ _ => normalize_univ_le _
  have hstep : ∀ n z, z Set.univ ≤ 1 → |V (n + 1) z - V n z| ≤ B * M.β ^ n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [hVdef, Function.iterate_zero, id, pow_zero, mul_one]
      unfold beliefBellman
      have e : (0 : Measure X → ℝ) z = ⨅ _ : U, (0 : ℝ) := by simp
      rw [e]
      apply inf_diff
      intro v
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
      exact beliefCost_bdd M B hB hBnn z hz v
    | succ n ih =>
      intro z hz
      have e : ∀ m, V (m + 1) = beliefBellman M (V m) := fun m =>
        Function.iterate_succ_apply' _ _ _
      have := bellman_lip M (V (n + 1)) (V n) (B * M.β ^ n) (by positivity)
        (fun F hF => ih F hF) z hz
      rw [← e (n + 1), ← e n] at this
      calc |V (n + 1 + 1) z - V (n + 1) z| ≤ M.β * (B * M.β ^ n) := this
        _ = B * M.β ^ (n + 1) := by ring
  have hconv : ∀ z, z Set.univ ≤ 1 → Tendsto (fun n => V n z) atTop (𝓝 (Jstar M z)) := by
    intro z hz
    have hc : CauchySeq (fun n => V n z) := by
      refine cauchySeq_of_le_geometric M.β B hβ1 fun n => ?_
      rw [Real.dist_eq, abs_sub_comm]
      exact hstep n z hz
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have : Jstar M z = L := hL.limUnder_eq
    rw [this]; exact hL
  have h1 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (Jstar M z)) :=
    (hconv z hz).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => V (n + 1) z) atTop (𝓝 (beliefBellman M (Jstar M) z)) := by
    have e : (fun n => V (n + 1) z) = fun n => ⨅ u : U, (beliefCost M z u + M.β *
        ∑ y : Y, obsProb M z u y * V n (filterUpdate M z u y)) := by
      funext n
      simp only [hVdef]
      rw [Function.iterate_succ_apply']
      rfl
    rw [e]
    unfold beliefBellman
    refine (inf_lip.tendsto _).comp (tendsto_pi_nhds.2 fun u => ?_)
    refine tendsto_const_nhds.add (Tendsto.const_mul _ (tendsto_finsetSum _ fun y _ => ?_))
    exact (hconv _ (hFU z u y)).const_mul _
  exact tendsto_nhds_unique h1 h2

end JS

end Aux_FMQ_eq33

open FiniteMemQL.Convergence Aux_FMQ_eq33 in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (π : Measure X) [IsProbabilityMeasure π] (I : Window Y U N) :
    JstarW M π I = ⨅ u : U, (chat M π I u +
      M.β * ∑ y : Y, predY M π I u y * JstarW M (nextPrior M π I u) (shift I u y)) := by
  unfold JstarW
  rw [jstar_fix M (post M π I) (normalize_univ_le _)]
  unfold beliefBellman
  refine iInf_congr fun u => ?_
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  show obsProb M (post M π I) u y * Jstar M (filterUpdate M (post M π I) u y) =
    obsProb M (post M π I) u y * Jstar M (post M (nextPrior M π I u) (shift I u y))
  by_cases hc : correct M π (I.1 0) Set.univ = 0
  · have hm : unnormPost M N π I = 0 :=
      Measure.measure_univ_eq_zero.1 (le_antisymm ((unnormPost_univ_le_correct M N π I).trans
        hc.le) zero_le)
    have hp : post M π I = 0 := by
      unfold post FiniteMemQL.Convergence.normalize; rw [hm, smul_zero]
    have h0 : obsProb M (post M π I) u y = 0 := by
      unfold obsProb
      rw [le_antisymm ((correct_univ_le M _ y).trans (by rw [predict_univ, hp]; simp)) zero_le]
      rfl
    rw [h0, zero_mul, zero_mul]
  · rw [post_nextPrior M π I u y hc]
