-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:46:04.567482+00:00
-- url     : https://prove2.me/submissions/7cd87e7c-273c-4d5d-b056-90f7d38e85b6

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_lemma_13
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_eq_7
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_properties_1_4
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_step_d_kl_bound

open MeasureTheory InformationTheory
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

namespace CLB8

variable {M α T : ℕ} {U : Type} [MeasurableSpace U]

lemma interactionLaw_prob (μU : Measure U) [IsProbabilityMeasure μU]
    (P : Measure (Fin M → Act M α → ℝ)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (interactionLaw μU P T) := by
  unfold interactionLaw; infer_instance

lemma integrable_act (μU : Measure U) [IsProbabilityMeasure μU]
    (P : Measure (Fin M → Act M α → ℝ)) [IsProbabilityMeasure P] (π : Policy M (Act M α) U)
    (ctx : Fin T → Fin M) (s : Fin T) (f : Act M α → ℝ) :
    Integrable (fun ω => f (action (feedbackGraph M α) π ctx ω.1 ω.2 s))
      (interactionLaw μU P T) := by
  haveI := interactionLaw_prob (T := T) μU P
  refine Integrable.of_bound (C := ∑ b, |f b|)
    ((measurable_of_countable f).comp (CLBM.measurable_action _ π ctx s)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun b => |f b|) (fun b _ => abs_nonneg _) (Finset.mem_univ _)

lemma real_eq_integral (μU : Measure U) [IsProbabilityMeasure μU]
    (P : Measure (Fin M → Act M α → ℝ)) [IsProbabilityMeasure P] (π : Policy M (Act M α) U)
    (ctx : Fin T → Fin M) (s : Fin T) (p : Act M α → Prop) [DecidablePred p] :
    (interactionLaw μU P T {ω | p (action (feedbackGraph M α) π ctx ω.1 ω.2 s)}).toReal =
      ∫ ω, (if p (action (feedbackGraph M α) π ctx ω.1 ω.2 s) then (1 : ℝ) else 0)
        ∂(interactionLaw μU P T) := by
  have hS : MeasurableSet {ω : U × (Fin T → Fin M → Act M α → ℝ) |
      p (action (feedbackGraph M α) π ctx ω.1 ω.2 s)} :=
    (CLBM.measurable_action _ π ctx s) (Set.to_countable {a | p a}).measurableSet
  have : (fun ω : U × (Fin T → Fin M → Act M α → ℝ) =>
      if p (action (feedbackGraph M α) π ctx ω.1 ω.2 s) then (1 : ℝ) else 0) =
      Set.indicator {ω | p (action (feedbackGraph M α) π ctx ω.1 ω.2 s)} 1 := by
    funext ω; simp [Set.indicator]
  rw [this, integral_indicator_one hS]
  rfl

lemma opt_ge_mean (P : Measure (Fin M → Act M α → ℝ)) (c : Fin M) (a : Act M α) :
    meanReward P c a ≤ optReward P c :=
  le_ciSup (Set.finite_range _).bddAbove a

lemma sum_le_regret (μU : Measure U) [IsProbabilityMeasure μU]
    (P : Measure (Fin M → Act M α → ℝ)) [IsProbabilityMeasure P] (π : Policy M (Act M α) U)
    (ctx : Fin T → Fin M) (w : Fin T → Act M α → ℝ)
    (hw : ∀ t a, w t a ≤ optReward P (ctx t) - meanReward P (ctx t) a) :
    ∑ t, ∫ ω, w t (action (feedbackGraph M α) π ctx ω.1 ω.2 t) ∂(interactionLaw μU P T) ≤
      expectedRegret (feedbackGraph M α) P μU π ctx := by
  unfold expectedRegret regret
  rw [integral_finset_sum _ (fun t _ => integrable_act μU P π ctx t
    (fun a => optReward P (ctx t) - meanReward P (ctx t) a))]
  apply Finset.sum_le_sum
  intro t _
  apply integral_mono (integrable_act μU P π ctx t (w t))
    (integrable_act μU P π ctx t (fun a => optReward P (ctx t) - meanReward P (ctx t) a))
  intro ω
  exact hw t _

end CLB8

namespace CLB8

variable {M α T : ℕ} {U : Type} [MeasurableSpace U]

/-- Step (a): regret ≥ Δ · P(j_t ≠ u_{c_t}). -/
lemma gap_le_regret (hT : (α + 1) * M ≤ T) (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) (ctx : Fin T → Fin M) (u : Fin M → Fin (α + 1)) :
    ∑ t, gap M α T * (interactionLaw μU (hardLaw M α T u) T
        {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 t).2 ≠ u (ctx t)}).toReal ≤
      expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π ctx := by
  classical
  haveI := CLBH.hardLaw_prob M α T hT u
  have hp := properties_1_4 M α T hT u
  have h := sum_le_regret μU (hardLaw M α T u) π ctx
    (fun t a => gap M α T * (if a.2 ≠ u (ctx t) then 1 else 0)) (by
      intro t a
      by_cases ha : a.2 ≠ u (ctx t)
      · rw [if_pos ha, mul_one]
        exact hp.2.2.1 (ctx t) a (fun h => ha (by rw [h]))
      · rw [if_neg ha, mul_zero]
        linarith [opt_ge_mean (hardLaw M α T u) (ctx t) a])
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_const_mul, real_eq_integral μU (hardLaw M α T u) π ctx t
    (fun a => a.2 ≠ u (ctx t))]

/-- The key pointwise inequality used to bound the exponent (p. 23). -/
lemma pointwise_key (hα : 1 ≤ α) (γ cs : Fin M) (hγ : γ ≤ cs) (a : Act M α) :
    (1 / (α : ℝ)) * ∑ i : Fin α, (if a.1 < γ ∨ a = (γ, i.succ) then (1 : ℝ) else 0) ≤
      (if a.1 ≠ cs then 1 else 0) + (1 / (α : ℝ)) * (if cs = γ then 1 else 0) := by
  classical
  have hαpos : (0 : ℝ) < α := by exact_mod_cast hα
  have hcount : ∑ i : Fin α, (if a = (γ, i.succ) then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    have : (Finset.univ.filter (fun i : Fin α => a = (γ, i.succ))).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      have := hi.symm.trans hj
      exact Fin.succ_injective _ (Prod.ext_iff.mp this).2
    exact_mod_cast this
  rcases lt_trichotomy a.1 γ with h | h | h
  · have hne : a.1 ≠ cs := fun e => absurd (e ▸ h) (not_lt.mpr hγ)
    simp only [h, true_or, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hne, ne_eq, not_false_eq_true]
    rw [one_div, inv_mul_cancel₀ hαpos.ne']
    have : 0 ≤ (α : ℝ)⁻¹ * (if cs = γ then 1 else 0) := by positivity
    linarith
  · have hsimp : ∀ i : Fin α, (if a.1 < γ ∨ a = (γ, i.succ) then (1 : ℝ) else 0) =
        (if a = (γ, i.succ) then 1 else 0) := by
      intro i; simp [h]
    simp_rw [hsimp]
    have hl : (1 / (α : ℝ)) * ∑ i : Fin α, (if a = (γ, i.succ) then (1 : ℝ) else 0) ≤ 1 / α :=
      by
        have := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ 1 / α)
        linarith
    have h1α : 1 / (α : ℝ) ≤ 1 := by
      rw [div_le_one hαpos]; exact_mod_cast hα
    by_cases hc : cs = γ
    · simp only [hc, if_true, mul_one]
      have : (0 : ℝ) ≤ if a.1 ≠ γ then 1 else 0 := by split_ifs <;> norm_num
      linarith
    · have hne : a.1 ≠ cs := by rw [h]; exact Ne.symm hc
      simp only [hne, ne_eq, not_false_eq_true, if_true, hc, if_false, mul_zero, add_zero]
      linarith
  · have hsimp : ∀ i : Fin α, (if a.1 < γ ∨ a = (γ, i.succ) then (1 : ℝ) else 0) = 0 := by
      intro i
      rw [if_neg]
      rintro (h' | h')
      · exact absurd h' (not_lt.mpr h.le)
      · rw [h'] at h; exact lt_irrefl _ h
    simp_rw [hsimp]
    simp only [Finset.sum_const_zero, mul_zero]
    have : (0 : ℝ) ≤ if a.1 ≠ cs then 1 else 0 := by split_ifs <;> norm_num
    have : 0 ≤ (1 / (α : ℝ)) * (if cs = γ then 1 else 0) := by positivity
    linarith

end CLB8

namespace CLB8

variable {M α T : ℕ} {U : Type} [MeasurableSpace U]

lemma block_mono (hM : 0 < M) (s t : Fin T) (h : s.val ≤ t.val) :
    blockContext M T hM t ≤ blockContext M T hM s := by
  simp only [blockContext, Fin.mk_le_mk]
  exact Nat.sub_le_sub_left (Nat.div_le_div_right h) _

lemma block_count (hM : 0 < M) (hMT : M ∣ T) (t : Fin T) :
    (Finset.univ.filter (fun s : Fin T => s.val < t.val ∧
      blockContext M T hM s = blockContext M T hM t)).card ≤ T / M := by
  set B := T / M with hB
  have hTMB : T = M * B := (Nat.mul_div_cancel' hMT).symm
  have hBpos : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · exfalso
      have h2 : T = 0 := by rw [hTMB, h, mul_zero]
      have := t.isLt
      omega
    · exact h
  have hlt : ∀ s : Fin T, s.val / B < M := by
    intro s
    rw [Nat.div_lt_iff_lt_mul hBpos, ← hTMB]; exact s.isLt
  calc _ ≤ (Finset.range B).card := by
        apply Finset.card_le_card_of_injOn (fun s : Fin T => s.val % B)
        · intro s _
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hBpos))
        · intro s hs s' hs' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs hs'
          have e1 := congrArg Fin.val hs.2
          have e2 := congrArg Fin.val hs'.2
          simp only [blockContext] at e1 e2
          have h1 := hlt s; have h2 := hlt s'; have h3 := hlt t
          have hq : s.val / B = s'.val / B := by
            rw [hB] at h1 h2 h3 ⊢; omega
          apply Fin.ext
          rw [← Nat.div_add_mod s.val B, ← Nat.div_add_mod s'.val B, hq]
          simp only at heq
          rw [heq]
    _ = B := Finset.card_range B

/-- Bound on the averaged exponent (pp. 23–24). -/
lemma exponent_bound (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    (μU : Measure U) [IsProbabilityMeasure μU] (π : Policy M (Act M α) U)
    (u0 : Fin M → Fin (α + 1)) (t : Fin T) :
    (1 / (α : ℝ)) * ∑ i : Fin α, ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t.val),
        (interactionLaw μU (hardLaw M α T u0) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 s).1 <
                blockContext M T hM t ∨
              action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 s =
                (blockContext M T hM t, i.succ)}).toReal ≤
      4 * expectedRegret (feedbackGraph M α) (hardLaw M α T u0) μU π (blockContext M T hM) +
        (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ) := by
  classical
  haveI := CLBH.hardLaw_prob M α T hT u0
  set ctx := blockContext M T hM with hctx
  set γ := ctx t
  set L := interactionLaw μU (hardLaw M α T u0) T with hL
  haveI : IsProbabilityMeasure L := interactionLaw_prob μU _
  set S := Finset.univ.filter (fun s : Fin T => s.val < t.val) with hS
  set act := fun (ω : U × (Fin T → Fin M → Act M α → ℝ)) (s : Fin T) =>
    action (feedbackGraph M α) π ctx ω.1 ω.2 s with hact
  have hαpos : (0 : ℝ) < α := by exact_mod_cast hα
  -- rewrite probabilities as integrals and swap
  have hLHS : (1 / (α : ℝ)) * ∑ i : Fin α, ∑ s ∈ S,
        (L {ω | (act ω s).1 < γ ∨ act ω s = (γ, i.succ)}).toReal =
      ∑ s ∈ S, ∫ ω, (1 / (α : ℝ)) * ∑ i : Fin α,
        (if (act ω s).1 < γ ∨ act ω s = (γ, i.succ) then (1 : ℝ) else 0) ∂L := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_act μU (hardLaw M α T u0) π ctx s
      (fun a => if a.1 < γ ∨ a = (γ, i.succ) then (1 : ℝ) else 0))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact real_eq_integral μU (hardLaw M α T u0) π ctx s (fun a => a.1 < γ ∨ a = (γ, i.succ))
  have hpt : ∀ s ∈ S, ∫ ω, (1 / (α : ℝ)) * ∑ i : Fin α,
        (if (act ω s).1 < γ ∨ act ω s = (γ, i.succ) then (1 : ℝ) else 0) ∂L ≤
      (L {ω | (act ω s).1 ≠ ctx s}).toReal + (1 / (α : ℝ)) * (if ctx s = γ then 1 else 0) := by
    intro s hs
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hγ : γ ≤ ctx s := block_mono hM s t hs.le
    rw [real_eq_integral μU (hardLaw M α T u0) π ctx s (fun a => a.1 ≠ ctx s)]
    have hi := integrable_act μU (hardLaw M α T u0) π ctx s
      (fun a => if a.1 ≠ ctx s then (1 : ℝ) else 0)
    calc _ ≤ ∫ ω, ((if (act ω s).1 ≠ ctx s then (1 : ℝ) else 0) +
            (1 / (α : ℝ)) * (if ctx s = γ then 1 else 0)) ∂L := by
          apply integral_mono
          · exact integrable_act μU (hardLaw M α T u0) π ctx s (fun a => (1 / (α : ℝ)) * ∑ i : Fin α,
              (if a.1 < γ ∨ a = (γ, i.succ) then (1 : ℝ) else 0))
          · exact hi.add (integrable_const _)
          · intro ω
            exact pointwise_key hα γ (ctx s) hγ (act ω s)
      _ = _ := by
          rw [integral_add hi (integrable_const _), integral_const]
          simp
  have h7 := eq_7 M α T hM hT μU π u0
  have hsum1 : ∑ s ∈ S, (L {ω | (act ω s).1 ≠ ctx s}).toReal ≤
      ∑ s, (L {ω | (act ω s).1 ≠ ctx s}).toReal :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)
  have hsum2 : ∑ s ∈ S, (1 / (α : ℝ)) * (if ctx s = γ then 1 else 0) ≤
      (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_boole, Finset.filter_filter]
    exact_mod_cast block_count hM hMT t
  rw [hLHS]
  calc _ ≤ ∑ s ∈ S, ((L {ω | (act ω s).1 ≠ ctx s}).toReal +
          (1 / (α : ℝ)) * (if ctx s = γ then 1 else 0)) := Finset.sum_le_sum hpt
    _ = ∑ s ∈ S, (L {ω | (act ω s).1 ≠ ctx s}).toReal +
          ∑ s ∈ S, (1 / (α : ℝ)) * (if ctx s = γ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

end CLB8

namespace CLB8

variable {M α T : ℕ} {U : Type} [MeasurableSpace U]

/-- Steps (b)–(e) for a fixed round `t` and a fixed value of the other coordinates `v`. -/
lemma bayes_step (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    (μU : Measure U) [IsProbabilityMeasure μU] (π : Policy M (Act M α) U)
    (v : Fin M → Fin (α + 1)) (t : Fin T) (R : ℝ)
    (hR : expectedRegret (feedbackGraph M α)
      (hardLaw M α T (Function.update v (blockContext M T hM t) 0)) μU π
      (blockContext M T hM) ≤ R) :
    (1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * R + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)))) ≤
      (1 / ((α : ℝ) + 1)) * ∑ k : Fin (α + 1),
        (interactionLaw μU (hardLaw M α T (Function.update v (blockContext M T hM t) k)) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).2 ≠ k}).toReal := by
  classical
  set ctx := blockContext M T hM with hctx
  set γ := ctx t with hγ
  set uk := fun k : Fin (α + 1) => Function.update v γ k with huk
  have hαpos : (0 : ℝ) < α := by exact_mod_cast hα
  have ht : t.val ≤ T := Nat.le_of_lt t.isLt
  set H := fun ω : U × (Fin T → Fin M → Act M α → ℝ) =>
    (ω.1, observations (feedbackGraph M α) π ctx ω.1 ω.2 t.val ht) with hHdef
  have hH : Measurable H :=
    measurable_fst.prodMk (CLBM.measurable_observations (feedbackGraph M α) π ctx t.val ht)
  set Q := fun k : Fin (α + 1) => (interactionLaw μU (hardLaw M α T (uk k)) T).map H with hQdef
  have hQ : ∀ k, IsProbabilityMeasure (Q k) := by
    intro k
    haveI := CLBH.hardLaw_prob M α T hT (uk k)
    haveI := interactionLaw_prob (T := T) μU (hardLaw M α T (uk k))
    exact Measure.isProbabilityMeasure_map hH.aemeasurable
  set Ψ := fun h : U × (Fin t.val → Fin M → Act M α → ℝ) =>
    (π.act t.val h.1 (fun i => ctx ⟨i.val, by omega⟩) h.2).2 with hΨdef
  have hΨ : Measurable Ψ :=
    measurable_snd.comp ((π.measurable_act t.val).comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  have h13 := lemma_13 α Q hQ Ψ hΨ
  have hQk : ∀ k, (Q k {h | Ψ h ≠ k}).toReal =
      (interactionLaw μU (hardLaw M α T (uk k)) T
        {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 t).2 ≠ k}).toReal := by
    intro k
    simp only [hQdef]
    rw [show {h | Ψ h ≠ k} = Ψ ⁻¹' {x | x ≠ k} from rfl,
      Measure.map_apply hH (hΨ (Set.to_countable {x : Fin (α + 1) | x ≠ k}).measurableSet)]
    rfl
  simp_rw [hQk] at h13
  -- the KL bounds
  set D := fun i : Fin α => 64 / 3 * gap M α T ^ 2 *
    ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t.val),
      (interactionLaw μU (hardLaw M α T (uk 0)) T
        {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 s).1 < γ ∨
          action (feedbackGraph M α) π ctx ω.1 ω.2 s = (γ, i.succ)}).toReal with hDdef
  have hD0 : ∀ i, 0 ≤ D i := by
    intro i
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hKL : ∀ i : Fin α, klDiv (Q 0) (Q i.succ) ≤ ENNReal.ofReal (D i) := by
    intro i
    have hu : uk i.succ γ ≠ 0 := by simp [huk, Fin.succ_ne_zero]
    have h := step_d_kl_bound M α T hT μU π ctx (uk i.succ) γ hu t.val ht
    have e1 : Function.update (uk i.succ) γ 0 = uk 0 := by simp [huk]
    have e2 : uk i.succ γ = i.succ := by simp [huk]
    rw [e1, e2] at h
    exact h
  have hterm : ∀ i : Fin α, Real.exp (-D i) ≤
      (if klDiv (Q 0) (Q i.succ) = ⊤ then 0 else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) := by
    intro i
    have hne : klDiv (Q 0) (Q i.succ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKL i)
    rw [if_neg hne]
    apply Real.exp_le_exp.mpr
    have := ENNReal.toReal_le_of_le_ofReal (hD0 i) (hKL i)
    linarith
  -- Jensen
  have hJ : Real.exp (-((1 / (α : ℝ)) * ∑ i : Fin α, D i)) ≤
      (1 / (α : ℝ)) * ∑ i : Fin α, Real.exp (-D i) := by
    have := (convexOn_exp).map_sum_le (t := Finset.univ) (w := fun _ : Fin α => 1 / (α : ℝ))
      (p := fun i => -D i) (fun _ _ => by positivity)
      (by simp [Finset.card_univ]; field_simp) (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at this
    rw [← Finset.mul_sum, ← Finset.mul_sum] at this
    calc Real.exp (-((1 / (α : ℝ)) * ∑ i : Fin α, D i))
        = Real.exp ((1 / (α : ℝ)) * ∑ i : Fin α, -D i) := by
          rw [Finset.sum_neg_distrib]; ring_nf
      _ ≤ _ := this
  -- exponent bound
  have hE := exponent_bound hα hM hT hMT μU π (uk 0) t
  have hE' : (1 / (α : ℝ)) * ∑ i : Fin α, D i ≤
      64 / 3 * gap M α T ^ 2 * (4 * R + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)) := by
    have hEq : (1 / (α : ℝ)) * ∑ i : Fin α, D i = 64 / 3 * gap M α T ^ 2 *
        ((1 / (α : ℝ)) * ∑ i : Fin α, ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t.val),
          (interactionLaw μU (hardLaw M α T (uk 0)) T
            {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 s).1 < γ ∨
              action (feedbackGraph M α) π ctx ω.1 ω.2 s = (γ, i.succ)}).toReal) := by
      simp only [hDdef, ← Finset.mul_sum]; ring
    rw [hEq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hR' : expectedRegret (feedbackGraph M α) (hardLaw M α T (uk 0)) μU π ctx ≤ R := hR
    linarith
  -- combine
  set E := 64 / 3 * gap M α T ^ 2 * (4 * R + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ))
  have h1 : Real.exp (-E) ≤ Real.exp (-((1 / (α : ℝ)) * ∑ i : Fin α, D i)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : (α : ℝ) * Real.exp (-E) ≤ ∑ i : Fin α, Real.exp (-D i) := by
    have := le_trans h1 hJ
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hαpos] at this
    linarith
  have h3 : ∑ i : Fin α, Real.exp (-D i) ≤ ∑ i : Fin α,
      (if klDiv (Q 0) (Q i.succ) = ⊤ then 0 else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have h4 : (1 / 4 : ℝ) * Real.exp (-E) ≤
      1 / (2 * ((α : ℝ) + 1)) * ((α : ℝ) * Real.exp (-E)) := by
    have hexp : 0 < Real.exp (-E) := Real.exp_pos _
    rw [show 1 / (2 * ((α : ℝ) + 1)) * ((α : ℝ) * Real.exp (-E)) =
      (α / (2 * (α + 1))) * Real.exp (-E) by ring]
    apply mul_le_mul_of_nonneg_right _ hexp.le
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ α := by exact_mod_cast hα
    linarith
  calc (1 / 4 : ℝ) * Real.exp (-E) ≤ 1 / (2 * ((α : ℝ) + 1)) * ((α : ℝ) * Real.exp (-E)) := h4
    _ ≤ 1 / (2 * ((α : ℝ) + 1)) * ∑ i : Fin α,
        (if klDiv (Q 0) (Q i.succ) = ⊤ then 0 else
          Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ ≤ _ := h13

end CLB8

namespace CLB8

variable {M α T : ℕ} {U : Type} [MeasurableSpace U]

lemma er_le_max (hM : 0 < M) (μU : Measure U) (π : Policy M (Act M α) U)
    (u : Fin M → Fin (α + 1)) :
    expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π (blockContext M T hM) ≤
      maxRegret M α T hM μU π := by
  unfold maxRegret
  exact le_ciSup (f := fun u : Fin M → Fin (α + 1) =>
    expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π (blockContext M T hM))
    (Set.finite_range _).bddAbove u

lemma split_update (γ : Fin M) (k : Fin (α + 1))
    (w : ∀ j : {j : Fin M // j ≠ γ}, Fin (α + 1)) :
    Function.update ((Equiv.piSplitAt γ (fun _ => Fin (α + 1))).symm (0, w)) γ k =
      (Equiv.piSplitAt γ (fun _ => Fin (α + 1))).symm (k, w) := by
  funext j
  by_cases h : j = γ
  · subst h; simp [Equiv.piSplitAt_symm_apply]
  · simp [Equiv.piSplitAt_symm_apply, Function.update, h]

lemma split_apply (γ : Fin M) (k : Fin (α + 1))
    (w : ∀ j : {j : Fin M // j ≠ γ}, Fin (α + 1)) :
    (Equiv.piSplitAt γ (fun _ => Fin (α + 1))).symm (k, w) γ = k := by
  simp [Equiv.piSplitAt_symm_apply]

/-- Averaging over `u` (p. 23): for each round, the average error probability is at least
`(1/4) exp(-E)`. -/
lemma avg_step (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    (μU : Measure U) [IsProbabilityMeasure μU] (π : Policy M (Act M α) U) (t : Fin T) :
    ∑ _u : Fin M → Fin (α + 1), (1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * maxRegret M α T hM μU π + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)))) ≤
      ∑ u : Fin M → Fin (α + 1),
        (interactionLaw μU (hardLaw M α T u) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).2 ≠
            u (blockContext M T hM t)}).toReal := by
  set γ := blockContext M T hM t with hγ
  set e := Equiv.piSplitAt γ (fun _ : Fin M => Fin (α + 1)) with he
  set C := (1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * maxRegret M α T hM μU π + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)))) with hC
  rw [← e.symm.sum_comp, ← e.symm.sum_comp, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  apply Finset.sum_le_sum
  intro w _
  have hb := bayes_step hα hM hT hMT μU π (e.symm (0, w)) t (maxRegret M α T hM μU π)
    (er_le_max hM μU π _)
  have hrw : ∀ k : Fin (α + 1),
      (interactionLaw μU (hardLaw M α T (Function.update (e.symm (0, w)) γ k)) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).2 ≠ k}).toReal =
      (interactionLaw μU (hardLaw M α T (e.symm (k, w))) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).2 ≠
            e.symm (k, w) (blockContext M T hM t)}).toReal := by
    intro k
    rw [he, split_update, ← hγ, split_apply]
  simp only [← hγ] at hb
  simp only [hrw] at hb
  have hαpos : (0 : ℝ) < (α : ℝ) + 1 := by positivity
  have hsC : ∑ _k : Fin (α + 1), C = ((α : ℝ) + 1) * C := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsC]
  revert hb
  generalize (∑ k : Fin (α + 1),
      (interactionLaw μU (hardLaw M α T (e.symm (k, w))) T
          {ω | (action (feedbackGraph M α) π (blockContext M T hM) ω.1 ω.2 t).2 ≠
            e.symm (k, w) (blockContext M T hM t)}).toReal) = S
  intro hb
  calc ((α : ℝ) + 1) * C = ((α : ℝ) + 1) * ((1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * maxRegret M α T hM μU π + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ))))) := by
        rw [hC]
    _ ≤ ((α : ℝ) + 1) * (1 / ((α : ℝ) + 1) * S) := mul_le_mul_of_nonneg_left hb hαpos.le
    _ = S := by field_simp

end CLB8

namespace CLB8

theorem eq8_main (M α T : ℕ) (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) :
    gap M α T * T * ((1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * maxRegret M α T hM μU π + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ))))) ≤
      maxRegret M α T hM μU π := by
  set R := maxRegret M α T hM μU π
  set C := (1 / 4 : ℝ) * Real.exp (-(64 / 3 * gap M α T ^ 2 *
        (4 * R + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)))) with hC
  set ctx := blockContext M T hM
  set N := Fintype.card (Fin M → Fin (α + 1)) with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  have hΔ := CLBH.gap_nonneg M α T
  have h1 : ∑ u : Fin M → Fin (α + 1),
      expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π ctx ≤ N * R := by
    calc _ ≤ ∑ _u : Fin M → Fin (α + 1), R :=
          Finset.sum_le_sum (fun u _ => er_le_max hM μU π u)
      _ = N * R := by simp [hN]
  have h2 : ∑ u : Fin M → Fin (α + 1), ∑ t : Fin T, gap M α T *
      (interactionLaw μU (hardLaw M α T u) T
        {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 t).2 ≠ u (ctx t)}).toReal ≤
      ∑ u : Fin M → Fin (α + 1),
        expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π ctx :=
    Finset.sum_le_sum (fun u _ => gap_le_regret hT μU π ctx u)
  have h3 : ∑ _t : Fin T, gap M α T * ∑ _u : Fin M → Fin (α + 1), C ≤
      ∑ u : Fin M → Fin (α + 1), ∑ t : Fin T, gap M α T *
      (interactionLaw μU (hardLaw M α T u) T
        {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 t).2 ≠ u (ctx t)}).toReal := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    refine le_trans (mul_le_mul_of_nonneg_left (avg_step hα hM hT hMT μU π t) hΔ)
      (le_of_eq ?_)
    rw [Finset.mul_sum]
  have h4 : ∑ _t : Fin T, gap M α T * ∑ _u : Fin M → Fin (α + 1), C =
      N * (gap M α T * T * C) := by
    simp [hN]; ring
  have : N * (gap M α T * T * C) ≤ N * R := by linarith
  exact le_of_mul_le_mul_left this hNpos

end CLB8

open CLB8 in
theorem solution (M α T : ℕ) (hα : 1 ≤ α) (hM : 0 < M) (hT : (α + 1) * M ≤ T) (hMT : M ∣ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) :
    Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / 16 *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))
            - 4 * ((α : ℝ) + 1) / (3 * α)) ≤
        maxRegret M α T hM μU π ∧
      Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / (16 * Real.exp 3) *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))) ≤
        Real.sqrt ((((α + 1) * M : ℕ) : ℝ) * T) / 16 *
          Real.exp (-(16 * (((α + 1) * M : ℕ) : ℝ) * maxRegret M α T hM μU π / (3 * T))
            - 4 * ((α : ℝ) + 1) / (3 * α)) := by
  set R := maxRegret M α T hM μU π
  set K : ℝ := (((α + 1) * M : ℕ) : ℝ) with hKdef
  have hKpos' : 0 < (α + 1) * M := by positivity
  have hTpos' : 0 < T := lt_of_lt_of_le hKpos' hT
  have hKpos : 0 < K := by rw [hKdef]; exact_mod_cast hKpos'
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hTpos'
  have hαpos : (0 : ℝ) < α := by exact_mod_cast (show 0 < α by omega)
  have hα1 : (1 : ℝ) ≤ α := by exact_mod_cast hα
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hK : K = ((α : ℝ) + 1) * M := by rw [hKdef]; push_cast; ring
  have hTM : ((T / M : ℕ) : ℝ) = (T : ℝ) / M := by
    rw [Nat.cast_div hMT (by exact_mod_cast hM.ne')]
  have hgap2 : gap M α T ^ 2 = K / (16 * T) := by
    unfold gap; rw [Real.sq_sqrt (by positivity)]
  have hgapT : gap M α T * T = Real.sqrt (K * T) / 4 := by
    unfold gap
    rw [show K * T = (K / (16 * T)) * (4 * T) ^ 2 by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have hexp : 64 / 3 * gap M α T ^ 2 * (4 * R + (1 / (α : ℝ)) * ((T / M : ℕ) : ℝ)) =
      16 * K * R / (3 * T) + 4 * ((α : ℝ) + 1) / (3 * α) := by
    rw [hgap2, hTM]
    have hK' := hK
    field_simp
    rw [hK]; ring
  have hmain := eq8_main M α T hα hM hT hMT μU π
  rw [hexp, hgapT] at hmain
  constructor
  · calc _ = Real.sqrt (K * T) / 4 * ((1 / 4 : ℝ) *
          Real.exp (-(16 * K * R / (3 * T) + 4 * ((α : ℝ) + 1) / (3 * α)))) := by
          rw [show -(16 * K * R / (3 * T)) - 4 * ((α : ℝ) + 1) / (3 * α) =
            -(16 * K * R / (3 * T) + 4 * ((α : ℝ) + 1) / (3 * α)) by ring]
          ring
      _ ≤ R := hmain
  · have hq : 4 * ((α : ℝ) + 1) / (3 * α) ≤ 3 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [Real.exp_sub, div_eq_mul_inv (Real.exp _), mul_comm (Real.exp _)]
    rw [show Real.sqrt (K * T) / (16 * Real.exp 3) =
      Real.sqrt (K * T) / 16 * (Real.exp 3)⁻¹ by field_simp]
    have hs : 0 ≤ Real.sqrt (K * T) / 16 := by positivity
    have he : 0 < Real.exp (-(16 * K * R / (3 * T))) := Real.exp_pos _
    have hinv : (Real.exp 3)⁻¹ ≤ (Real.exp (4 * ((α : ℝ) + 1) / (3 * α)))⁻¹ := by
      apply inv_anti₀ (Real.exp_pos _)
      exact Real.exp_le_exp.mpr hq
    calc Real.sqrt (K * T) / 16 * (Real.exp 3)⁻¹ * Real.exp (-(16 * K * R / (3 * T)))
        ≤ Real.sqrt (K * T) / 16 * (Real.exp (4 * ((α : ℝ) + 1) / (3 * α)))⁻¹ *
            Real.exp (-(16 * K * R / (3 * T))) := by gcongr
      _ = _ := by ring
