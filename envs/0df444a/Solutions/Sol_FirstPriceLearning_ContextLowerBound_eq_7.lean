-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:12:11.277528+00:00
-- url     : https://prove2.me/submissions/c102f2dc-c8b3-4565-8727-551f899e4761

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory
open FirstPriceLearning.ContextLowerBound

namespace CLBH

lemma gap_nonneg (M α T : ℕ) : 0 ≤ gap M α T := Real.sqrt_nonneg _

lemma gap_le (M α T : ℕ) (hT : (α + 1) * M ≤ T) : gap M α T ≤ 1 / 4 := by
  unfold gap
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    have : ((((α + 1) * M : ℕ)) : ℝ) ≤ T := by exact_mod_cast hT
    linarith

lemma gap_pos (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T) : 0 < gap M α T := by
  unfold gap
  apply Real.sqrt_pos.mpr
  have hK : 0 < (α + 1) * M := by positivity
  have hTp : 0 < T := lt_of_lt_of_le hK hT
  have h1 : (0 : ℝ) < (((α + 1) * M : ℕ) : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < T := by exact_mod_cast hTp
  positivity

lemma hardMean_bounds (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : 0 ≤ hardMean M α T u c a ∧ hardMean M α T u c a ≤ 1 := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  unfold hardMean
  split_ifs <;> constructor <;> linarith

lemma bern_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (bernoulliReal p) := by
  constructor
  simp only [bernoulliReal, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

lemma integral_bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∫ x, x ∂(bernoulliReal p) = p := by
  unfold bernoulliReal
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [ENNReal.toReal_ofReal h0]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma hardLaw_prob (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsProbabilityMeasure (hardLaw M α T u) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  unfold hardLaw
  infer_instance

lemma map_coord (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) :
    (hardLaw M α T u).map (fun x => x c a) = bernoulliReal (hardMean M α T u c a) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  have h1 := (measurePreserving_eval
    (fun c => Measure.pi fun a => bernoulliReal (hardMean M α T u c a)) c).map_eq
  have h2 := (measurePreserving_eval (fun a => bernoulliReal (hardMean M α T u c a)) a).map_eq
  have : (fun x : Fin M → Act M α → ℝ => x c a) =
      (Function.eval a : (Act M α → ℝ) → ℝ) ∘ (Function.eval c : (Fin M → Act M α → ℝ) → _) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply a) (measurable_pi_apply c)]
  unfold hardLaw
  rw [h1, h2]

lemma meanReward_hard (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : meanReward (hardLaw M α T u) c a = hardMean M α T u c a := by
  unfold meanReward
  have hm : Measurable (fun x : Fin M → Act M α → ℝ => x c a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply c)
  have := integral_map (μ := hardLaw M α T u) hm.aemeasurable
    (aestronglyMeasurable_id (μ := (hardLaw M α T u).map (fun x => x c a)))
  simp only [id] at this
  rw [← this, map_coord M α T hT u c a]
  exact integral_bern _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2

end CLBH
namespace CLBH

/-- The maximal mean reward under context `c` is attained at `(c, u c)`. -/
lemma hardMean_le_opt (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) (ha : a ≠ (c, u c)) :
    hardMean M α T u c a + gap M α T ≤ hardMean M α T u c (c, u c) ∧
    (a.1 ≠ c → hardMean M α T u c a + 1 / 4 ≤ hardMean M α T u c (c, u c)) := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  obtain ⟨i, j⟩ := a
  have hne : ¬ (i = c ∧ j = u c) := fun h => ha (Prod.ext h.1 h.2)
  unfold hardMean
  simp only
  by_cases hic : i = c
  · subst hic
    have hj : j ≠ u i := fun h => hne ⟨rfl, h⟩
    refine ⟨?_, fun h => absurd rfl h⟩
    simp only [if_true]
    split_ifs <;> first | linarith | (exfalso; simp_all) | simp_all
  · refine ⟨?_, fun _ => ?_⟩ <;> simp only [hic, if_false, if_true] <;> split_ifs <;> linarith

lemma opt_eq (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M) :
    optReward (hardLaw M α T u) c = hardMean M α T u c (c, u c) := by
  haveI : Nonempty (Act M α) := ⟨(c, u c)⟩
  unfold optReward
  simp_rw [meanReward_hard M α T hT u c]
  apply le_antisymm
  · apply ciSup_le
    intro a
    by_cases ha : a = (c, u c)
    · rw [ha]
    · have := (hardMean_le_opt M α T hT u c a ha).1
      linarith [gap_nonneg M α T]
  · exact le_ciSup (Set.finite_range _).bddAbove (c, u c)

end CLBH

namespace CLBM

variable {M : ℕ} {A U : Type} [MeasurableSpace A] [MeasurableSpace U] [Countable A]
  [MeasurableSingletonClass A]

lemma measurable_reveal_comp {Ω : Type} [MeasurableSpace Ω] (E : A → A → Prop) {a : Ω → A}
    {x : Ω → Fin M → A → ℝ} (ha : Measurable a) (hx : Measurable x) :
    Measurable (fun ω => reveal E (a ω) (x ω)) := by
  classical
  refine measurable_pi_lambda _ (fun c => measurable_pi_lambda _ (fun b => ?_))
  simp only [reveal]
  refine Measurable.ite ?_ ((measurable_pi_apply b).comp ((measurable_pi_apply c).comp hx))
    measurable_const
  exact ha (Set.to_countable {a' : A | FirstPriceLearning.GraphFeedback.Revealed E a' b}).measurableSet

lemma measurable_observations (E : A → A → Prop) (π : Policy M A U) {T : ℕ}
    (c : Fin T → Fin M) :
    ∀ (t : ℕ) (h : t ≤ T),
      Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) => observations E π c ω.1 ω.2 t h) := by
  intro t
  induction t with
  | zero => intro h; exact measurable_pi_lambda _ (fun i => i.elim0)
  | succ t ih =>
    intro h
    have hprev := ih (Nat.le_of_succ_le h)
    have hact : Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) =>
        π.act t ω.1 (fun i => c ⟨i.val, by omega⟩)
          (observations E π c ω.1 ω.2 t (Nat.le_of_succ_le h))) := by
      have := π.measurable_act t
      exact this.comp (measurable_fst.prodMk (measurable_const.prodMk hprev))
    have hnew : Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) =>
        reveal E (π.act t ω.1 (fun i => c ⟨i.val, by omega⟩)
          (observations E π c ω.1 ω.2 t (Nat.le_of_succ_le h))) (ω.2 ⟨t, h⟩)) :=
      measurable_reveal_comp E hact ((measurable_pi_apply _).comp measurable_snd)
    simp only [observations]
    refine measurable_pi_lambda _ (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hnew
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp hprev

lemma measurable_action (E : A → A → Prop) (π : Policy M A U) {T : ℕ}
    (c : Fin T → Fin M) (t : Fin T) :
    Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) => action E π c ω.1 ω.2 t) := by
  have := π.measurable_act t.val
  exact this.comp (measurable_fst.prodMk
    (measurable_const.prodMk (measurable_observations E π c t.val (Nat.le_of_lt t.isLt))))

end CLBM

theorem solution (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) (u : Fin M → Fin (α + 1)) :
    (1 / 4 : ℝ) * ∑ t : Fin T,
        (interactionLaw μU (hardLaw M α T u) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).1 ≠
              blockContext M T hM t}).toReal ≤
      expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π (blockContext M T hM) := by
  classical
  haveI := CLBH.hardLaw_prob M α T hT u
  set c := blockContext M T hM
  set L := interactionLaw μU (hardLaw M α T u) T with hL
  haveI : IsProbabilityMeasure L := by rw [hL]; unfold interactionLaw; infer_instance
  set act := fun (ω : U × (Fin T → Fin M → Act M α → ℝ)) (t : Fin T) =>
    action (feedbackGraph M α) π c ω.1 ω.2 t with hact
  have hmeas : ∀ t, Measurable (fun ω => act ω t) := fun t =>
    CLBM.measurable_action (feedbackGraph M α) π c t
  set S := fun t : Fin T => {ω : U × (Fin T → Fin M → Act M α → ℝ) | (act ω t).1 ≠ c t}
  have hS : ∀ t, MeasurableSet (S t) := fun t =>
    hmeas t (Set.to_countable {a : Act M α | a.1 ≠ c t}).measurableSet
  -- per-round regret term
  set g := fun (t : Fin T) (a : Act M α) =>
    optReward (hardLaw M α T u) (c t) - meanReward (hardLaw M α T u) (c t) a
  have hg_nonneg : ∀ t a, 0 ≤ g t a := by
    intro t a
    simp only [g]
    rw [CLBH.opt_eq M α T hT u, CLBH.meanReward_hard M α T hT u]
    by_cases ha : a = (c t, u (c t))
    · rw [ha]; simp
    · linarith [(CLBH.hardMean_le_opt M α T hT u (c t) a ha).1, CLBH.gap_nonneg M α T]
  have hg_le : ∀ t a, g t a ≤ 1 := by
    intro t a
    simp only [g]
    rw [CLBH.opt_eq M α T hT u, CLBH.meanReward_hard M α T hT u]
    linarith [(CLBH.hardMean_bounds M α T hT u (c t) a).1,
      (CLBH.hardMean_bounds M α T hT u (c t) (c t, u (c t))).2]
  have hg_quarter : ∀ t a, a.1 ≠ c t → 1 / 4 ≤ g t a := by
    intro t a ha
    have ha' : a ≠ (c t, u (c t)) := fun h => ha (by rw [h])
    simp only [g]
    rw [CLBH.opt_eq M α T hT u, CLBH.meanReward_hard M α T hT u]
    linarith [(CLBH.hardMean_le_opt M α T hT u (c t) a ha').2 ha]
  have hterm_meas : ∀ t, Measurable (fun ω => g t (act ω t)) := fun t =>
    (measurable_of_countable (g t)).comp (hmeas t)
  have hint_term : ∀ t, Integrable (fun ω => g t (act ω t)) L := by
    intro t
    refine Integrable.of_bound (C := 1) (hterm_meas t).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hg_nonneg t (act ω t)], hg_le t (act ω t)⟩
  have hreg : expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π c =
      ∑ t, ∫ ω, g t (act ω t) ∂L := by
    unfold expectedRegret regret
    rw [← integral_finset_sum _ (fun t _ => hint_term t)]
  rw [hreg, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hind : (L (S t)).toReal = ∫ ω, (S t).indicator (fun _ => (1 : ℝ)) ω ∂L := by
    rw [show (S t).indicator (fun _ => (1 : ℝ)) = (S t).indicator 1 from rfl,
      integral_indicator_one (hS t)]; rfl
  rw [hind, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun ω => by
      simp only [Set.indicator]; split_ifs <;> norm_num)
  · exact hint_term t
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [Set.indicator]
    split_ifs with h
    · have := hg_quarter t (act ω t) h
      linarith
    · simp only [mul_zero]; exact hg_nonneg t (act ω t)
