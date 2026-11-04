-- Prove2me | solution 1 for CappedBaseStock.window_jensen_certificate
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:44:53.830401+00:00
-- url     : https://prove2.me/submissions/58c65598-77f2-4555-9f7a-eb2aac4adb38

import Definitions.Def_CappedBaseStock_Window
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/- Fully proved helper module: CappedWindowIntegrals -/
noncomputable section
open MeasureTheory CappedBaseStock
open scoped ENNReal NNReal BigOperators

namespace CappedWindowIntegrals

def realInventory (d : DemandPath) (r z : ℝ) : ℕ → ℝ
  | 0 => z
  | k + 1 => max 0 (realInventory d r z k + r - (d k : ℝ))


lemma measurable_windowDelivery (n k : ℕ) :
    Measurable (fun w : WindowInput n => windowDelivery w k) := by
  unfold windowDelivery
  split_ifs <;> fun_prop

lemma measurable_windowInventory (n m : ℕ) :
    Measurable (fun wd : WindowInput n × DemandPath =>
      windowInventory wd.1 wd.2 m) := by
  induction m with
  | zero => exact measurable_fst.fst
  | succ m ih =>
    simp only [windowInventory]
    exact (ih.add ((measurable_windowDelivery n m).comp measurable_fst)).sub
      ((measurable_pi_apply m).comp measurable_snd)

lemma measurable_windowInventory_fiber {n : ℕ} (d : DemandPath) (m : ℕ) :
    Measurable (fun w : WindowInput n => windowInventory w d m) :=
  (measurable_windowInventory n m).comp (measurable_id.prodMk measurable_const)

lemma integrable_windowDelivery {n : ℕ} (W : WindowLaw n) (k : ℕ) :
    Integrable (fun w : WindowInput n => (windowDelivery w k : ℝ)) W.law := by
  unfold windowDelivery
  split_ifs with hk
  · exact W.delivery_integrable ⟨k, hk⟩
  · simp only [NNReal.coe_zero]
    exact integrable_const 0

lemma integrable_windowInventory_fiber {n : ℕ} (W : WindowLaw n)
    (d : DemandPath) (m : ℕ) :
    Integrable (fun w : WindowInput n => (windowInventory w d m : ℝ)) W.law := by
  induction m with
  | zero => exact W.inventory_integrable
  | succ m ih =>
    apply (ih.add (integrable_windowDelivery W m)).mono'
    · exact ((measurable_windowInventory_fiber d (m + 1)).coe_nnreal_real).aestronglyMeasurable
    · filter_upwards [] with w
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      change ((windowInventory w d m + windowDelivery w m - d m : ℝ≥0) : ℝ) ≤ _
      exact_mod_cast (tsub_le_self : windowInventory w d m + windowDelivery w m - d m ≤
        windowInventory w d m + windowDelivery w m)

lemma integrable_windowInventory_prod (P : DemandLaw) {n : ℕ} (W : WindowLaw n)
    (m : ℕ) :
    Integrable (fun wd : WindowInput n × DemandPath =>
      (windowInventory wd.1 wd.2 m : ℝ)) (W.law.prod (demandPathLaw P)) := by
  induction m with
  | zero => exact W.inventory_integrable.comp_fst (demandPathLaw P)
  | succ m ih =>
    apply (ih.add ((integrable_windowDelivery W m).comp_fst (demandPathLaw P))).mono'
    · exact ((measurable_windowInventory n (m + 1)).coe_nnreal_real).aestronglyMeasurable
    · filter_upwards [] with wd
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      change ((windowInventory wd.1 wd.2 m + windowDelivery wd.1 m - wd.2 m : ℝ≥0) : ℝ) ≤ _
      exact_mod_cast (tsub_le_self : windowInventory wd.1 wd.2 m + windowDelivery wd.1 m - wd.2 m ≤
        windowInventory wd.1 wd.2 m + windowDelivery wd.1 m)

lemma integral_windowDelivery {n : ℕ} (W : WindowLaw n) (r z : ℝ)
    (hmeans : WindowMeans W r z) (k : ℕ) (hk : k < n) :
    (∫ w, (windowDelivery w k : ℝ) ∂W.law) = r := by
  simpa only [windowDelivery, dif_pos hk] using hmeans.2 ⟨k, hk⟩

lemma integrable_window_affine {n : ℕ} (W : WindowLaw n) (d : DemandPath) (k : ℕ) :
    Integrable (fun w : WindowInput n => (w.1 : ℝ) +
      ∑ i ∈ Finset.range k, ((windowDelivery w i : ℝ) - (d i : ℝ))) W.law := by
  exact W.inventory_integrable.add
    (integrable_finsetSum _ (fun i _ => (integrable_windowDelivery W i).sub (integrable_const _)))

lemma integral_window_affine {n : ℕ} (W : WindowLaw n) (r z : ℝ)
    (hmeans : WindowMeans W r z) (d : DemandPath) (k : ℕ) (hk : k ≤ n) :
    (∫ w, (w.1 : ℝ) + ∑ i ∈ Finset.range k,
        ((windowDelivery w i : ℝ) - (d i : ℝ)) ∂W.law) =
      z + (k : ℝ) * r - ∑ i ∈ Finset.range k, (d i : ℝ) := by
  have hterms : ∀ i ∈ Finset.range k,
      Integrable (fun w : WindowInput n => (windowDelivery w i : ℝ) - (d i : ℝ)) W.law :=
    fun i _ => (integrable_windowDelivery W i).sub (integrable_const _)
  have hsum : Integrable (fun w : WindowInput n =>
      ∑ i ∈ Finset.range k, ((windowDelivery w i : ℝ) - (d i : ℝ))) W.law :=
    integrable_finsetSum _ hterms
  rw [integral_add W.inventory_integrable hsum, hmeans.1,
    integral_finsetSum _ hterms]
  simp_rw [integral_sub (integrable_windowDelivery W _) (integrable_const _), integral_const,
    measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have heq : (∑ i ∈ Finset.range k, ((∫ w, (windowDelivery w i : ℝ) ∂W.law) - (d i : ℝ))) =
      ∑ i ∈ Finset.range k, (r - (d i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_windowDelivery W r z hmeans i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)]
  rw [heq, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma realInventory_le_integral_windowInventory {n : ℕ} (W : WindowLaw n)
    (r z : ℝ) (hmeans : WindowMeans W r z) (d : DemandPath)
    (m : ℕ) (hm : m ≤ n) :
    realInventory d r z m ≤ ∫ w, (windowInventory w d m : ℝ) ∂W.law := by
  induction m with
  | zero => simpa only [realInventory, windowInventory] using hmeans.1.ge
  | succ m ih =>
    have hmn : m < n := lt_of_lt_of_le (Nat.lt_succ_self m) hm
    have hprev := ih (Nat.le_of_lt hmn)
    apply max_le
    · exact integral_nonneg (fun w => NNReal.coe_nonneg _)
    · have hstep :
          (∫ w, (windowInventory w d m : ℝ) + (windowDelivery w m : ℝ) - (d m : ℝ) ∂W.law) ≤
            ∫ w, (windowInventory w d (m + 1) : ℝ) ∂W.law := by
        apply integral_mono
          (((integrable_windowInventory_fiber W d m).add (integrable_windowDelivery W m)).sub
            (integrable_const _))
          (integrable_windowInventory_fiber W d (m + 1))
        intro w
        simp only [windowInventory, NNReal.coe_sub_def, NNReal.coe_add]
        exact le_max_left _ _
      rw [integral_sub
          (f := fun w : WindowInput n => (windowInventory w d m : ℝ) + (windowDelivery w m : ℝ))
          (g := fun _ : WindowInput n => (d m : ℝ))
          ((integrable_windowInventory_fiber W d m).add (integrable_windowDelivery W m))
          (integrable_const _),
        integral_add (integrable_windowInventory_fiber W d m) (integrable_windowDelivery W m),
        integral_windowDelivery W r z hmeans m hmn, integral_const,
        measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hstep
      linarith

lemma measurable_realInventory (r z : ℝ) (m : ℕ) :
    Measurable (fun d : DemandPath => realInventory d r z m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    simp only [realInventory]
    exact measurable_const.max ((ih.add measurable_const).sub
      ((measurable_pi_apply m).coe_nnreal_real))

lemma realInventory_nonneg (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ realInventory d r z m := by
  cases m with
  | zero => exact hz
  | succ m => exact le_max_left _ _

lemma realInventory_le (d : DemandPath) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (m : ℕ) :
    realInventory d r z m ≤ z + (m : ℝ) * r := by
  induction m with
  | zero => simp [realInventory]
  | succ m ih =>
    simp only [realInventory, Nat.cast_add, Nat.cast_one]
    apply max_le
    · positivity
    · have hd := NNReal.coe_nonneg (d m)
      nlinarith

lemma integrable_realInventory (P : DemandLaw) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (m : ℕ) :
    Integrable (fun d : DemandPath => realInventory d r z m) (demandPathLaw P) := by
  apply (integrable_const (z + (m : ℝ) * r)).mono'
    (measurable_realInventory r z m).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_eq_abs, abs_of_nonneg (realInventory_nonneg d r z hz m)]
  exact realInventory_le d r z hr hz m

lemma ofReal_integral_windowInventory_prod (P : DemandLaw) {n : ℕ}
    (W : WindowLaw n) (m : ℕ) :
    ENNReal.ofReal (∫ wd : WindowInput n × DemandPath,
      (windowInventory wd.1 wd.2 m : ℝ) ∂(W.law.prod (demandPathLaw P))) =
      windowExpectedInventory P W m := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_windowInventory_prod P W m)
    (Filter.Eventually.of_forall (fun wd => NNReal.coe_nonneg _))]
  simp only [windowExpectedInventory, ENNReal.ofReal_coe_nnreal]

lemma integral_realInventory_le_windowInventory_prod (P : DemandLaw) {n : ℕ}
    (W : WindowLaw n) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (hmeans : WindowMeans W r z) (m : ℕ) (hm : m ≤ n) :
    (∫ d, realInventory d r z m ∂demandPathLaw P) ≤
      ∫ wd : WindowInput n × DemandPath,
        (windowInventory wd.1 wd.2 m : ℝ) ∂(W.law.prod (demandPathLaw P)) := by
  rw [integral_prod_symm _ (integrable_windowInventory_prod P W m)]
  apply integral_mono (integrable_realInventory P r z hr hz m)
    (integrable_windowInventory_prod P W m).integral_prod_right
  intro d
  exact realInventory_le_integral_windowInventory W r z hmeans d m hm

lemma ofReal_integral_realInventory_le (P : DemandLaw) {n : ℕ}
    (W : WindowLaw n) (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (hmeans : WindowMeans W r z) (m : ℕ) (hm : m ≤ n) :
    ENNReal.ofReal (∫ d, realInventory d r z m ∂demandPathLaw P) ≤
      windowExpectedInventory P W m := by
  rw [← ofReal_integral_windowInventory_prod P W m]
  exact ENNReal.ofReal_le_ofReal
    (integral_realInventory_le_windowInventory_prod P W r z hr hz hmeans m hm)

end CappedWindowIntegrals

end

/- Fully proved helper module: CappedDemandReversal -/
noncomputable section
open MeasureTheory CappedBaseStock
open scoped ENNReal NNReal BigOperators

namespace CappedDemandReversal

/-- Reverse the first `m` natural indices and fix every later index. -/
def reverseIndex (m k : ℕ) : ℕ := if k < m then m - 1 - k else k

lemma reverseIndex_involutive (m : ℕ) : Function.Involutive (reverseIndex m) := by
  intro k
  by_cases hk : k < m
  · have hr : m - 1 - k < m := by omega
    simp only [reverseIndex, if_pos hk, if_pos hr]
    omega
  · simp only [reverseIndex, if_neg hk]

/-- Reverse exactly the first `m` demands and leave the later path unchanged. -/
def finiteBlockReverse (m : ℕ) (d : DemandPath) (k : ℕ) : ℝ≥0 :=
  d (reverseIndex m k)

lemma finiteBlockReverse_apply_lt (m : ℕ) (d : DemandPath) (k : ℕ) (hk : k < m) :
    finiteBlockReverse m d k = d (m - 1 - k) := by
  simp [finiteBlockReverse, reverseIndex, hk]

lemma finiteBlockReverse_apply_ge (m : ℕ) (d : DemandPath) (k : ℕ) (hk : m ≤ k) :
    finiteBlockReverse m d k = d k := by
  simp [finiteBlockReverse, reverseIndex, Nat.not_lt.mpr hk]

lemma finiteBlockReverse_involutive (m : ℕ) :
    Function.Involutive (finiteBlockReverse m) := by
  intro d
  funext k
  exact congrArg d (reverseIndex_involutive m k)

lemma measurable_finiteBlockReverse (m : ℕ) : Measurable (finiteBlockReverse m) := by
  exact measurable_pi_lambda _ (fun k => measurable_pi_apply (reverseIndex m k))

/-- The reversal is a measurable equivalence, so even nonintegrable Bochner
integrands retain their usual convention under this change of variables. -/
def finiteBlockReverseEquiv (m : ℕ) : DemandPath ≃ᵐ DemandPath :=
  MeasurableEquiv.ofInvolutive _ (finiteBlockReverse_involutive m)
    (measurable_finiteBlockReverse m)

lemma measurePreserving_finiteBlockReverse (P : DemandLaw) (m : ℕ) :
    MeasurePreserving (finiteBlockReverse m) (demandPathLaw P) (demandPathLaw P) := by
  refine ⟨measurable_finiteBlockReverse m, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => P.law) (reverseIndex_involutive m).injective

lemma lintegral_finiteBlockReverse (P : DemandLaw) (m : ℕ)
    (f : DemandPath → ℝ≥0∞) :
    (∫⁻ d, f (finiteBlockReverse m d) ∂demandPathLaw P) =
      ∫⁻ d, f d ∂demandPathLaw P := by
  exact (measurePreserving_finiteBlockReverse P m).lintegral_comp_emb
    (finiteBlockReverseEquiv m).measurableEmbedding f

lemma integral_finiteBlockReverse (P : DemandLaw) (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : DemandPath → E) :
    (∫ d, f (finiteBlockReverse m d) ∂demandPathLaw P) =
      ∫ d, f d ∂demandPathLaw P := by
  exact (measurePreserving_finiteBlockReverse P m).integral_comp
    (finiteBlockReverseEquiv m).measurableEmbedding f

/-- Any sum of a common coordinate function over the reversed block is unchanged. -/
lemma sum_finiteBlockReverse {E : Type*} [AddCommMonoid E]
    (m : ℕ) (d : DemandPath) (f : ℝ≥0 → E) :
    (∑ k ∈ Finset.range m, f (finiteBlockReverse m d k)) =
      ∑ k ∈ Finset.range m, f (d k) := by
  calc
    _ = ∑ k ∈ Finset.range m, f (d (m - 1 - k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [finiteBlockReverse_apply_lt m d k (Finset.mem_range.mp hk)]
    _ = _ := Finset.sum_range_reflect (fun k => f (d k)) m

lemma sum_demand_finiteBlockReverse (m : ℕ) (d : DemandPath) :
    (∑ k ∈ Finset.range m, (finiteBlockReverse m d k : ℝ)) =
      ∑ k ∈ Finset.range m, (d k : ℝ) :=
  sum_finiteBlockReverse m d (fun x => (x : ℝ))

lemma sum_increment_finiteBlockReverse (m : ℕ) (d : DemandPath) (r : ℝ) :
    (∑ k ∈ Finset.range m, (r - (finiteBlockReverse m d k : ℝ))) =
      ∑ k ∈ Finset.range m, (r - (d k : ℝ)) :=
  sum_finiteBlockReverse m d (fun x => r - (x : ℝ))

lemma sum_excess_finiteBlockReverse (m : ℕ) (d : DemandPath) (r : ℝ) :
    (∑ k ∈ Finset.range m, ((finiteBlockReverse m d k : ℝ) - r)) =
      ∑ k ∈ Finset.range m, ((d k : ℝ) - r) :=
  sum_finiteBlockReverse m d (fun x => (x : ℝ) - r)

/-- A prefix of the reversed block is the corresponding suffix of the original block. -/
lemma sum_prefix_finiteBlockReverse {E : Type*} [AddCommMonoid E]
    (m k : ℕ) (hk : k ≤ m) (d : DemandPath) (f : ℝ≥0 → E) :
    (∑ i ∈ Finset.range k, f (finiteBlockReverse m d i)) =
      ∑ i ∈ Finset.Ico (m - k) m, f (d i) := by
  cases m with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ m =>
    calc
      _ = ∑ i ∈ Finset.range k, f (d (m - i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [finiteBlockReverse_apply_lt (m + 1) d i (by
          have := Finset.mem_range.mp hi
          omega)]
        simp
      _ = _ := by
        simpa only [← Nat.Ico_zero_eq_range, Nat.sub_zero] using
          (Finset.sum_Ico_reflect (fun i => f (d i)) 0 (m := k) (n := m) hk)

/-- The same reversal identity expressed as a difference of prefix sums. -/
lemma sum_prefix_finiteBlockReverse_sub {E : Type*} [AddCommGroup E]
    (m k : ℕ) (hk : k ≤ m) (d : DemandPath) (f : ℝ≥0 → E) :
    (∑ i ∈ Finset.range k, f (finiteBlockReverse m d i)) =
      (∑ i ∈ Finset.range m, f (d i)) -
        ∑ i ∈ Finset.range (m - k), f (d i) := by
  rw [sum_prefix_finiteBlockReverse m k hk d f]
  exact Finset.sum_Ico_eq_sub (fun i => f (d i)) (Nat.sub_le m k)

lemma sum_prefix_finiteBlockReverse_complement {E : Type*} [AddCommGroup E]
    (m k : ℕ) (hk : k ≤ m) (d : DemandPath) (f : ℝ≥0 → E) :
    (∑ i ∈ Finset.range m, f (d i)) -
        (∑ i ∈ Finset.range k, f (finiteBlockReverse m d i)) =
      ∑ i ∈ Finset.range (m - k), f (d i) := by
  rw [sum_prefix_finiteBlockReverse_sub m k hk d f]
  abel

lemma sum_range_reflect_complement {E : Type*} [AddCommGroup E]
    (f : ℕ → E) (m k : ℕ) (hk : k ≤ m) :
    (∑ i ∈ Finset.range m, f i) -
        (∑ i ∈ Finset.range k, f (m - 1 - i)) =
      ∑ i ∈ Finset.range (m - k), f i := by
  have hs : (∑ i ∈ Finset.range k, f (m - 1 - i)) =
      (∑ i ∈ Finset.range m, f i) - ∑ i ∈ Finset.range (m - k), f i := by
    cases m with
    | zero =>
      have : k = 0 := by omega
      subst k
      simp
    | succ m =>
      calc
        _ = ∑ i ∈ Finset.Ico (m + 1 - k) (m + 1), f i := by
          simpa only [← Nat.Ico_zero_eq_range, Nat.add_sub_cancel, Nat.sub_zero] using
            (Finset.sum_Ico_reflect f 0 (m := k) (n := m) hk)
        _ = _ := Finset.sum_Ico_eq_sub f (Nat.sub_le _ _)
  rw [hs]
  abel

/-- Reversing all indices from zero through m preserves their finite supremum. -/
lemma sup'_range_complement {E : Type*} [SemilatticeSup E]
    (f : ℕ → E) (m : ℕ) :
    (Finset.range (m + 1)).sup' (by simp) (fun k => f (m - k)) =
      (Finset.range (m + 1)).sup' (by simp) f := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro k hk
    exact Finset.le_sup' f (Finset.mem_range.mpr (by omega))
  · apply Finset.sup'_le
    intro k hk
    have hkm : k ≤ m := by
      have := Finset.mem_range.mp hk
      omega
    have hmem : m - k ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hback : m - (m - k) = k := by omega
    simpa only [hback] using (Finset.le_sup' (fun j => f (m - j)) hmem)

end CappedDemandReversal

end

/- Fully proved helper module: CappedWindowAlgebra -/
section

open CappedBaseStock Finset
open scoped BigOperators

namespace CappedWindowAlgebra

def partialSum (a : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ range m, a i

def reflectedSup (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  (range (m + 1)).sup' (by simp) (fun k => -partialSum a k)

lemma partialSum_zero (a : ℕ → ℝ) : partialSum a 0 = 0 := by simp [partialSum]

lemma partialSum_succ (a : ℕ → ℝ) (m : ℕ) :
    partialSum a (m + 1) = partialSum a m + a m := by
  simp [partialSum, sum_range_succ]

lemma reflectedSup_zero (a : ℕ → ℝ) : reflectedSup a 0 = 0 := by
  simp [reflectedSup, partialSum]

lemma reflectedSup_succ (a : ℕ → ℝ) (m : ℕ) :
    reflectedSup a (m + 1) = max (-partialSum a (m + 1)) (reflectedSup a m) := by
  unfold reflectedSup
  simpa only [range_add_one] using
    (Finset.sup'_insert (s := range (m + 1)) (by simp)
      (fun k => -partialSum a k) (b := m + 1))

theorem reflection_formula (a H : ℕ → ℝ) (z : ℝ) (hz : 0 ≤ z)
    (h0 : H 0 = z) (hs : ∀ m, H (m + 1) = max 0 (H m + a m)) (m : ℕ) :
    H m = partialSum a m + max z (reflectedSup a m) := by
  induction m with
  | zero => simp [h0, partialSum_zero, reflectedSup_zero, max_eq_left hz]
  | succ m ih =>
    rw [hs, ih, partialSum_succ, reflectedSup_succ, partialSum_succ]
    generalize partialSum a m = b
    generalize reflectedSup a m = s
    generalize a m = x
    simp only [max_def]
    split_ifs <;> linarith

theorem realInventory_reflection (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    CappedWindowIntegrals.realInventory d r z m =
      partialSum (fun i => r - (d i : ℝ)) m +
        max z (reflectedSup (fun i => r - (d i : ℝ)) m) := by
  apply reflection_formula _ _ z hz rfl
  intro k
  simp only [CappedWindowIntegrals.realInventory]
  congr 1
  ring

theorem realInventory_reverse_eq (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    CappedWindowIntegrals.realInventory (CappedDemandReversal.finiteBlockReverse m d) r z m =
      max (finiteInventory d r m) (z + partialSum (fun i => r - (d i : ℝ)) m) := by
  rw [realInventory_reflection _ r z hz m]
  have hfull : partialSum (fun i => r -
      (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) m =
      partialSum (fun i => r - (d i : ℝ)) m :=
    CappedDemandReversal.sum_increment_finiteBlockReverse m d r
  rw [hfull]
  have hsup : partialSum (fun i => r - (d i : ℝ)) m +
      reflectedSup (fun i => r - (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) m =
      finiteInventory d r m := by
    have hpoint (k : ℕ) (hk : k ∈ range (m + 1)) :
        partialSum (fun i => r - (d i : ℝ)) m -
          partialSum (fun i => r - (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) k =
            partialSum (fun i => r - (d i : ℝ)) (m - k) := by
      exact CappedDemandReversal.sum_prefix_finiteBlockReverse_complement m k
        (by have := mem_range.mp hk; omega) d (fun x => r - (x : ℝ))
    have hsup2 :
        (range (m + 1)).sup' (by simp)
          (fun k => partialSum (fun i => r - (d i : ℝ)) m -
            partialSum (fun i => r - (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) k) =
        finiteInventory d r m := by
      calc
        _ = (range (m + 1)).sup' (by simp)
            (fun k => partialSum (fun i => r - (d i : ℝ)) (m - k)) := by
          apply Finset.sup'_congr _ rfl
          exact hpoint
        _ = _ := CappedDemandReversal.sup'_range_complement
          (fun k => partialSum (fun i => r - (d i : ℝ)) k) m
    rw [← hsup2]
    unfold reflectedSup
    apply le_antisymm
    · apply add_le_of_le_sub_left
      apply Finset.sup'_le
      intro k hk
      have hle := Finset.le_sup'
        (fun k => partialSum (fun i => r - (d i : ℝ)) m -
          partialSum (fun i => r - (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) k) hk
      linarith
    · apply Finset.sup'_le
      intro k hk
      have hle := Finset.le_sup'
        (fun k => -partialSum (fun i => r - (CappedDemandReversal.finiteBlockReverse m d i : ℝ)) k) hk
      linarith
  rw [add_max, hsup]
  rw [max_comm]
  congr 1
  ring

theorem excess_real_identity (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    CappedWindowIntegrals.realInventory (CappedDemandReversal.finiteBlockReverse m d) r z m - z +
        (∑ i ∈ range m, ((d i : ℝ) - r)) =
      max 0 (finiteInventory d r m + (∑ i ∈ range m, ((d i : ℝ) - r)) - z) := by
  rw [realInventory_reverse_eq d r z hz m]
  have hsum : partialSum (fun i => r - (d i : ℝ)) m =
      -(∑ i ∈ range m, ((d i : ℝ) - r)) := by
    simp only [partialSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  generalize finiteInventory d r m = a
  generalize (∑ i ∈ range m, ((d i : ℝ) - r)) = b
  simp only [max_def]
  split_ifs <;> linarith

theorem excess_expression_nonneg (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ CappedWindowIntegrals.realInventory (CappedDemandReversal.finiteBlockReverse m d) r z m - z +
        (∑ i ∈ range m, ((d i : ℝ) - r)) := by
  rw [excess_real_identity d r z hz m]
  exact le_max_left _ _

theorem certificateExcess_identity (d : DemandPath) (r z : ℝ) (hz : 0 ≤ z) (m : ℕ) :
    certificateExcess d r z m =
      ENNReal.ofReal (CappedWindowIntegrals.realInventory
        (CappedDemandReversal.finiteBlockReverse m d) r z m - z +
          (∑ i ∈ range m, ((d i : ℝ) - r))) := by
  rw [excess_real_identity d r z hz m]
  simp [certificateExcess, ENNReal.ofReal_max]

end CappedWindowAlgebra

end

/- Fully proved helper module: CappedJensenFinish -/
noncomputable section
open MeasureTheory CappedBaseStock CappedWindowIntegrals CappedDemandReversal
open scoped ENNReal NNReal BigOperators

namespace CappedJensenFinish

lemma integrable_demand_coordinate (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => (d i : ℝ)) (demandPathLaw P) := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i).integrable_comp_of_integrable
    P.finiteMean

lemma integral_demand_coordinate (P : DemandLaw) (i : ℕ) :
    (∫ d : DemandPath, (d i : ℝ) ∂demandPathLaw P) = mean P := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i
  change (∫ d : DemandPath, ((Function.eval i d : ℝ≥0) : ℝ)
    ∂Measure.infinitePi (fun _ : ℕ => P.law)) = ∫ x : ℝ≥0, (x : ℝ) ∂P.law
  conv_rhs => rw [← hmp.map_eq]
  exact (integral_map_of_stronglyMeasurable hmp.measurable
    (by fun_prop : StronglyMeasurable (fun x : ℝ≥0 => (x : ℝ)))).symm

lemma integrable_sum_demand_excess (P : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : DemandPath =>
      ∑ i ∈ Finset.range m, ((d i : ℝ) - r)) (demandPathLaw P) := by
  exact integrable_finsetSum _ (fun i _ =>
    (integrable_demand_coordinate P i).sub (integrable_const r))

lemma integral_sum_demand_excess (P : DemandLaw) (r : ℝ) (m : ℕ) :
    (∫ d : DemandPath, ∑ i ∈ Finset.range m, ((d i : ℝ) - r) ∂demandPathLaw P) =
      (m : ℝ) * (mean P - r) := by
  have hterms : ∀ i ∈ Finset.range m,
      Integrable (fun d : DemandPath => (d i : ℝ) - r) (demandPathLaw P) :=
    fun i _ => (integrable_demand_coordinate P i).sub (integrable_const r)
  rw [integral_finsetSum _ hterms]
  simp_rw [integral_sub (integrable_demand_coordinate P _) (integrable_const r),
    integral_demand_coordinate, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  simp [mul_sub]

lemma integrable_reverse_inventory_excess (P : DemandLaw) (r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (m : ℕ) :
    Integrable (fun d : DemandPath =>
      realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r)) (demandPathLaw P) := by
  exact (((measurePreserving_finiteBlockReverse P m).integrable_comp_of_integrable
    (integrable_realInventory P r z hr hz m)).sub (integrable_const z)).add
      (integrable_sum_demand_excess P r m)

lemma integral_reverse_inventory_excess (P : DemandLaw) (r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (m : ℕ) :
    (∫ d : DemandPath, realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r) ∂demandPathLaw P) =
      (∫ d, realInventory d r z m ∂demandPathLaw P) - z +
        (m : ℝ) * (mean P - r) := by
  have hrev : Integrable (fun d : DemandPath => realInventory (finiteBlockReverse m d) r z m)
      (demandPathLaw P) :=
    (measurePreserving_finiteBlockReverse P m).integrable_comp_of_integrable
      (integrable_realInventory P r z hr hz m)
  rw [integral_add
    (f := fun d : DemandPath => realInventory (finiteBlockReverse m d) r z m - z)
    (g := fun d : DemandPath => ∑ i ∈ Finset.range m, ((d i : ℝ) - r))
    (hrev.sub (integrable_const z)) (integrable_sum_demand_excess P r m),
    integral_sub (g := fun _ : DemandPath => z) hrev (integrable_const z),
    integral_sum_demand_excess,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    integral_finiteBlockReverse P m (fun d => realInventory d r z m)]

lemma lintegral_certificateExcess_of_reverse_identity (P : DemandLaw) (r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (m : ℕ)
    (hexcess : ∀ d : DemandPath, certificateExcess d r z m =
      ENNReal.ofReal (realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r)))
    (hnonneg : ∀ d : DemandPath, 0 ≤
      realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r)) :
    (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) =
      ENNReal.ofReal ((∫ d, realInventory d r z m ∂demandPathLaw P) - z +
        (m : ℝ) * (mean P - r)) := by
  simp_rw [hexcess]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_reverse_inventory_excess P r z hr hz m)
    (Filter.Eventually.of_forall hnonneg)]
  rw [integral_reverse_inventory_excess P r z hr hz m]

lemma window_jensen_of_reverse_identity (P : DemandLaw) (n : ℕ) (W : WindowLaw n)
    (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (hmeans : WindowMeans W r z) (m : ℕ) (hmn : m ≤ n)
    (hbound : windowExpectedInventory P W m ≤ ENNReal.ofReal z)
    (hexcess : ∀ d : DemandPath, certificateExcess d r z m =
      ENNReal.ofReal (realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r)))
    (hnonneg : ∀ d : DemandPath, 0 ≤
      realInventory (finiteBlockReverse m d) r z m - z +
        ∑ i ∈ Finset.range m, ((d i : ℝ) - r)) :
    (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r)) := by
  rw [lintegral_certificateExcess_of_reverse_identity P r z hr hz m hexcess hnonneg]
  have hmean : (∫ d, realInventory d r z m ∂demandPathLaw P) ≤ z :=
    (ENNReal.ofReal_le_ofReal_iff hz).mp
      ((ofReal_integral_realInventory_le P W r z hr hz hmeans m hmn).trans hbound)
  apply ENNReal.ofReal_le_ofReal
  linarith

end CappedJensenFinish

end

open MeasureTheory CappedBaseStock CappedJensenFinish CappedWindowAlgebra
open scoped ENNReal

theorem solution (P : DemandLaw) (n : ℕ) (W : WindowLaw n)
    (r z : ℝ) (hr : 0 ≤ r) (hrmean : r ≤ mean P) (hz : 0 ≤ z)
    (hmeans : WindowMeans W r z) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hbound : windowExpectedInventory P W m ≤ ENNReal.ofReal z) :
    (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r)) := by
  exact window_jensen_of_reverse_identity P n W r z hr hz hmeans m hmn hbound
    (fun d => certificateExcess_identity d r z hz m)
    (fun d => excess_expression_nonneg d r z hz m)
