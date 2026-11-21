-- Prove2me | solution 1 for FreeOrderEPTAS.estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:21:19.820548+00:00
-- url     : https://prove2.me/submissions/77111b34-68e2-44a9-a452-4d33b77c76f6

import Mathlib
import Definitions.Def_FreeOrderEPTAS_OPT

open MeasureTheory

namespace Aux_VR

open FreeOrderEPTAS

/-- value of the backward recursion for laws `ν` taken in the natural order -/
noncomputable def Rv {n : ℕ} (ν : Fin n → Measure ℝ) (t : ℕ) : ℝ :=
  ((List.finRange n).drop t).foldr (fun s v => ∫ x, max x v ∂(ν s)) 0

lemma Rv_zero_succ {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) :
    Rv ν 0 = ∫ x, max x (Rv (fun j => ν j.succ) 0) ∂(ν 0) := by
  unfold Rv
  rw [List.finRange_succ]
  simp [List.foldr_map]

lemma Rv_shift {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) (t : ℕ) :
    Rv ν (t + 1) = Rv (fun j => ν j.succ) t := by
  unfold Rv
  rw [List.finRange_succ, List.drop_succ_cons, ← List.map_drop, List.foldr_map]

lemma Rv_ge_n {n : ℕ} (ν : Fin n → Measure ℝ) (t : ℕ) (ht : n ≤ t) : Rv ν t = 0 := by
  unfold Rv
  rw [List.drop_eq_nil_of_le (by simpa using ht)]
  rfl

lemma int_max (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (v : ℝ) :
    Integrable (fun x => max x v) μ := by
  refine Integrable.mono' (hμ.norm.add (integrable_const |v|))
    ((continuous_id.max continuous_const).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, id, Pi.add_apply]
  rcases le_total x v with h | h
  · rw [max_eq_right h]; linarith [abs_nonneg x]
  · rw [max_eq_left h]; linarith [abs_nonneg v]

lemma measurable_cons_fin {k : ℕ} (a : ℝ) :
    Measurable (fun obs : Fin k → ℝ => (Fin.cons a obs : Fin (k + 1) → ℝ)) := by
  apply measurable_pi_lambda
  intro s
  refine Fin.cases ?_ (fun s => ?_) s
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply s

/-- The rule after the first observation `a`. -/
def shiftRule {n : ℕ} (τ : StoppingRule (n + 1)) (a : ℝ) : StoppingRule n where
  stop t obs := τ.stop t.succ (Fin.cons a obs)
  measurable_stop t := (τ.measurable_stop t.succ).comp (measurable_cons_fin a)

lemma observed_one {n : ℕ} (y : Fin n → ℝ) (t : Fin n) (s : Fin (t.val + 1)) :
    observed 1 y t s = y ⟨s.val, by omega⟩ := rfl

lemma observed_cons_succ {n : ℕ} (a : ℝ) (z : Fin n → ℝ) (t : Fin n) :
    observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t.succ = Fin.cons a (observed 1 z t) := by
  funext s
  refine Fin.cases ?_ (fun s => ?_) s
  · rw [observed_one, Fin.cons_zero]
    have : (⟨(0 : Fin (t.val + 1 + 1)).val, by simp⟩ : Fin (n + 1)) = 0 := rfl
    rw [this, Fin.cons_zero]
  · rw [observed_one, Fin.cons_succ, observed_one]
    have : (⟨(Fin.succ s).val, by simp; omega⟩ : Fin (n + 1)) = Fin.succ ⟨s.val, by omega⟩ :=
      Fin.ext rfl
    rw [this, Fin.cons_succ]

lemma reward_zero (τ : StoppingRule 0) (y : Fin 0 → ℝ) : reward τ 1 y = 0 := by
  unfold reward stopTime
  simp

lemma reward_cons {n : ℕ} (τ : StoppingRule (n + 1)) (a : ℝ) (z : Fin n → ℝ) :
    reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ) =
      if τ.stop 0 (fun _ => a) then a else reward (shiftRule τ a) 1 z := by
  have h0 : observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0 = fun _ => a := by
    funext s
    rw [observed_one]
    have : (⟨s.val, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by
      have h1 := s.isLt
      simp only [Fin.val_zero, Fin.val_mk] at h1 ⊢
      omega)
    rw [this, Fin.cons_zero]
  unfold reward stopTime
  rw [List.finRange_succ]
  by_cases hs : τ.stop 0 (fun _ => a) = true
  · have hp0 : (fun t : Fin (n + 1) =>
        τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) 0 = true := by
      show τ.stop 0 (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0) = true
      rw [h0]; exact hs
    rw [List.find?_cons_of_pos (p := fun t : Fin (n + 1) =>
      τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) (a := 0)
      (l := List.map Fin.succ (List.finRange n)) hp0, if_pos hs]
    rfl
  · have hp0 : ¬ ((fun t : Fin (n + 1) =>
        τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) 0 = true) := by
      show ¬ τ.stop 0 (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) 0) = true
      rw [h0]; exact hs
    rw [List.find?_cons_of_neg (p := fun t : Fin (n + 1) =>
      τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) (a := 0)
      (l := List.map Fin.succ (List.finRange n)) hp0, if_neg hs, List.find?_map]
    have hp : ((fun t : Fin (n + 1) => τ.stop t (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t)) ∘
        Fin.succ) = fun t => (shiftRule τ a).stop t (observed 1 z t) := by
      funext t
      rw [Function.comp_apply]
      show τ.stop t.succ (observed 1 (Fin.cons a z : Fin (n + 1) → ℝ) t.succ) = _
      rw [observed_cons_succ]
      rfl
    rw [hp]
    cases h : List.find? (fun t => (shiftRule τ a).stop t (observed 1 z t)) (List.finRange n) with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      show (Fin.cons a z : Fin (n + 1) → ℝ) ((1 : Equiv.Perm (Fin (n + 1))) t.succ) =
        z ((1 : Equiv.Perm (Fin n)) t)
      simp

lemma reward_abs_le {n : ℕ} (τ : StoppingRule n) (y : Fin n → ℝ) :
    |reward τ 1 y| ≤ ∑ i, |y i| := by
  unfold reward
  split
  · exact Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ _)
  · simp only [abs_zero]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma measurable_observed {n : ℕ} (t : Fin n) :
    Measurable (fun y : Fin n → ℝ => observed 1 y t) := by
  apply measurable_pi_lambda
  intro s
  exact measurable_pi_apply _

lemma reward_eq_sum {n : ℕ} (τ : StoppingRule n) (y : Fin n → ℝ) :
    reward τ 1 y = ∑ t : Fin n,
      (if (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
        τ.stop t (observed 1 y t) = true then y t else 0) := by
  unfold reward stopTime
  cases h : List.find? (fun t => τ.stop t (observed 1 y t)) (List.finRange n) with
  | none =>
    rw [List.find?_eq_none] at h
    symm
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact h t (List.mem_finRange t) h2
  | some t0 =>
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨h1, i, hi, hget, hbefore⟩ := h
    have hi' : i = t0.val := by
      have := congrArg Fin.val hget
      simpa using this
    have hprev : ∀ s : Fin n, s < t0 → τ.stop s (observed 1 y s) = false := by
      intro s hs
      have hlt : s.val < i := by rw [hi']; exact hs
      have h2 := hbefore s.val hlt
      have hget' : (List.finRange n)[s.val]'(by rw [List.length_finRange]; exact s.isLt) = s := by
        apply Fin.ext; simp
      rw [hget'] at h2
      simpa using h2
    symm
    rw [Finset.sum_eq_single t0]
    · rw [if_pos ⟨hprev, h1⟩]; rfl
    · intro t _ ht
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · rw [hprev t hlt] at h3; exact absurd h3 (by simp)
      · have := h2 t0 hgt
        rw [this] at h1; exact absurd h1 (by simp)
    · intro h; exact absurd (Finset.mem_univ _) h

lemma reward_measurable {n : ℕ} (τ : StoppingRule n) : Measurable (reward τ 1) := by
  have hfun : reward τ 1 = fun y => ∑ t : Fin n,
      (if (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
        τ.stop t (observed 1 y t) = true then y t else 0) := funext (reward_eq_sum τ)
  rw [hfun]
  apply Finset.measurable_sum
  intro t _
  have hm : ∀ s : Fin n, Measurable (fun y : Fin n → ℝ => τ.stop s (observed 1 y s)) :=
    fun s => (τ.measurable_stop s).comp (measurable_observed s)
  refine Measurable.ite ?_ (measurable_pi_apply t) measurable_const
  have hset : {y : Fin n → ℝ | (∀ s : Fin n, s < t → τ.stop s (observed 1 y s) = false) ∧
      τ.stop t (observed 1 y t) = true} =
      (⋂ s : Fin n, {y | s < t → τ.stop s (observed 1 y s) = false}) ∩
        ((fun y => τ.stop t (observed 1 y t)) ⁻¹' {true}) := by
    ext y; simp
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun s => ?_) ((hm t) (measurableSet_singleton _))
  by_cases hst : s < t
  · have : {y : Fin n → ℝ | s < t → τ.stop s (observed 1 y s) = false} =
        (fun y => τ.stop s (observed 1 y s)) ⁻¹' {false} := by
      ext y; simp [hst]
    rw [this]; exact (hm s) (measurableSet_singleton _)
  · have : {y : Fin n → ℝ | s < t → τ.stop s (observed 1 y s) = false} = Set.univ := by
      ext y; simp [hst]
    rw [this]; exact MeasurableSet.univ

lemma reward_integrable {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n) :
    Integrable (reward τ 1) (Measure.pi ν) := by
  have hsum : Integrable (fun y : Fin n → ℝ => ∑ i, |y i|) (Measure.pi ν) := by
    apply integrable_finset_sum
    intro i _
    exact (integrable_eval (μ := ν) (hint i)).abs
  refine Integrable.mono' hsum (reward_measurable τ).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs]
  exact reward_abs_le τ y

/-- The key step: splitting off the first coordinate. -/
lemma integral_split {n : ℕ} (ν : Fin (n + 1) → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule (n + 1)) :
    Integrable (fun a => ∫ z, reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ)
      ∂(Measure.pi fun j => ν j.succ)) (ν 0) ∧
    ∫ y, reward τ 1 y ∂(Measure.pi ν) =
      ∫ a, ∫ z, reward τ 1 (Fin.cons a z : Fin (n + 1) → ℝ) ∂(Measure.pi fun j => ν j.succ)
        ∂(ν 0) := by
  have hmp := (measurePreserving_piFinSuccAbove ν 0).symm
  have hI := reward_integrable ν hP hint τ
  have hI2 : Integrable (fun p : ℝ × (Fin n → ℝ) => reward τ 1 (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ))
      ((ν 0).prod (Measure.pi fun j => ν j.succ)) := by
    have := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hI
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero',
      Function.comp_def] using this
  refine ⟨hI2.integral_prod_left, ?_⟩
  calc ∫ y, reward τ 1 y ∂(Measure.pi ν)
      = ∫ p, reward τ 1 ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm p)
          ∂((ν 0).prod (Measure.pi fun j => ν j.succ)) := (hmp.integral_comp' _).symm
    _ = ∫ p, reward τ 1 (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)
          ∂((ν 0).prod (Measure.pi fun j => ν j.succ)) := by
        congr 1
        funext p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    _ = _ := integral_prod _ hI2

theorem bound : ∀ (n : ℕ) (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n),
    ∫ y, reward τ 1 y ∂(Measure.pi ν) ≤ Rv ν 0 := by
  intro n
  induction n with
  | zero =>
    intro ν hP hint τ
    simp [reward_zero, Rv]
  | succ n ih =>
    intro ν hP hint τ
    obtain ⟨hIa, hE⟩ := integral_split ν hP hint τ
    rw [hE, Rv_zero_succ]
    haveI := hP 0
    apply integral_mono hIa (int_max (ν 0) (hint 0) _)
    intro a
    simp only [reward_cons]
    by_cases hs : τ.stop 0 (fun _ => a) = true
    · haveI : ∀ j, IsProbabilityMeasure ((fun j : Fin n => ν j.succ) j) := fun j => hP j.succ
      simp only [hs, if_true]
      simp
    · simp only [hs, if_false, Bool.false_eq_true]
      have := ih (fun j => ν j.succ) (fun j => hP j.succ) (fun j => hint j.succ) (shiftRule τ a)
      exact le_trans this (le_max_right _ _)

theorem attained : ∀ (n : ℕ) (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (τ : StoppingRule n)
    (hτ : ∀ t obs, τ.stop t obs = decide (Rv ν (t.val + 1) ≤ obs (Fin.last t.val))),
    ∫ y, reward τ 1 y ∂(Measure.pi ν) = Rv ν 0 := by
  intro n
  induction n with
  | zero =>
    intro ν hP hint τ _
    simp [reward_zero, Rv]
  | succ n ih =>
    intro ν hP hint τ hτ
    obtain ⟨_, hE⟩ := integral_split ν hP hint τ
    rw [hE, Rv_zero_succ]
    apply integral_congr_ae
    filter_upwards with a
    simp only [reward_cons]
    have hτ' : ∀ (t : Fin n) obs, (shiftRule τ a).stop t obs =
        decide (Rv (fun j => ν j.succ) (t.val + 1) ≤ obs (Fin.last t.val)) := by
      intro t obs
      show τ.stop t.succ (Fin.cons a obs) = _
      rw [hτ]
      have e1 : (Fin.cons a obs : Fin (t.val + 1 + 1) → ℝ) (Fin.last (t.succ.val)) =
          obs (Fin.last t.val) := by
        have : (Fin.last (t.succ.val) : Fin (t.val + 1 + 1)) = Fin.succ (Fin.last t.val) := rfl
        rw [this, Fin.cons_succ]
      rw [e1]
      congr 2
      have := Rv_shift ν (t.val + 1)
      simpa using this
    have h0 : τ.stop 0 (fun _ => a) = decide (Rv (fun j => ν j.succ) 0 ≤ a) := by
      rw [hτ]
      have := Rv_shift ν 0
      simp only [Fin.val_zero, zero_add] at this ⊢
      rw [this]
    rw [h0]
    have hrec := ih (fun j => ν j.succ) (fun j => hP j.succ) (fun j => hint j.succ)
      (shiftRule τ a) hτ'
    by_cases hc : Rv (fun j => ν j.succ) 0 ≤ a
    · haveI : ∀ j, IsProbabilityMeasure ((fun j : Fin n => ν j.succ) j) := fun j => hP j.succ
      simp [hc, max_eq_left hc]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false]
      rw [hrec, max_eq_right (le_of_lt (lt_of_not_ge hc))]


lemma Rv_nonneg {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) : ∀ L : List (Fin n),
    0 ≤ L.foldr (fun s v => ∫ x, max x v ∂(ν s)) 0 := by
  intro L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.foldr_cons]
    haveI := hP s
    have h := integral_mono (integrable_const (L.foldr (fun s v => ∫ x, max x v ∂(ν s)) 0))
      (int_max (ν s) (hint s) _) (fun x => le_max_right x _)
    simp at h
    linarith

/-- the threshold rule (a local copy) -/
noncomputable def thr {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) : StoppingRule n where
  stop t obs := decide (Rv (fun i => I.μ (σ i)) (t.val + 1) ≤ obs (Fin.last t.val))
  measurable_stop t := by
    refine measurable_to_bool ?_
    have : (fun obs : Fin (t.val + 1) → ℝ => decide (Rv (fun i => I.μ (σ i)) (t.val + 1) ≤ obs (Fin.last t.val))) ⁻¹'
        {true} = {obs | Rv (fun i => I.μ (σ i)) (t.val + 1) ≤ obs (Fin.last t.val)} := by
      ext obs; simp
    rw [this]
    exact measurableSet_le measurable_const (measurable_pi_apply _)

theorem V_eq_R {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    V I σ = Rv (fun i => I.μ (σ i)) 0 := by
  set ν : Fin n → Measure ℝ := fun i => I.μ (σ i) with hν
  have hP : ∀ i, IsProbabilityMeasure (ν i) := fun i => I.prob (σ i)
  have hint : ∀ i, Integrable id (ν i) := fun i => I.integrable (σ i)
  have hreward : ∀ (τ : StoppingRule n) (x : Fin n → ℝ),
      reward τ σ x = reward τ 1 (fun i => x (σ i)) := fun τ x => rfl
  have hmp := (measurePreserving_piCongrLeft I.μ σ).symm
  have hint_eq : ∀ τ : StoppingRule n,
      ∫ x, reward τ σ x ∂(Measure.pi I.μ) = ∫ y, reward τ 1 y ∂(Measure.pi ν) := by
    intro τ
    calc ∫ x, reward τ σ x ∂(Measure.pi I.μ)
        = ∫ x, reward τ 1 ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm x)
            ∂(Measure.pi I.μ) := by
          congr 1
      _ = ∫ y, reward τ 1 y ∂(Measure.pi ν) := hmp.integral_comp' _
  have hle : ∀ τ : StoppingRule n, ∫ x, reward τ σ x ∂(Measure.pi I.μ) ≤ Rv ν 0 := by
    intro τ
    rw [hint_eq]
    exact bound n ν hP hint τ
  have heq : ∫ x, reward (thr I σ) σ x ∂(Measure.pi I.μ) = Rv ν 0 := by
    rw [hint_eq]
    exact attained n ν hP hint _ (fun t obs => rfl)
  unfold V
  haveI : Nonempty (StoppingRule n) := ⟨thr I σ⟩
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← heq]
    exact le_ciSup ⟨Rv ν 0, by rintro _ ⟨τ, rfl⟩; exact hle τ⟩ (thr I σ)

end Aux_VR

namespace Aux_EST

open FreeOrderEPTAS MeasureTheory

lemma int_sub_max (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (v : ℝ) :
    Integrable (fun x => max (x - v) 0) μ := by
  refine Integrable.mono' (hμ.norm.add (integrable_const |v|))
    (((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, id, Pi.add_apply]
  rcases le_total (x - v) 0 with h | h
  · rw [max_eq_right h]; simp; positivity
  · rw [max_eq_left h, abs_of_nonneg h]
    have h1 := le_abs_self x
    have h2 := neg_abs_le v
    linarith

/-- one step of the threshold lower bound -/
lemma step_lb (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (T v : ℝ) :
    ∫ x, max (x - T) 0 ∂μ + v + (T - v) * (μ {x | T ≤ x}).toReal ≤ ∫ x, max x v ∂μ := by
  have hs : MeasurableSet {x : ℝ | T ≤ x} := measurableSet_Ici
  have hind : Integrable (fun x => (T - v) * Set.indicator {x : ℝ | T ≤ x} 1 x) μ :=
    ((integrable_const (1 : ℝ)).indicator hs).const_mul (T - v)
  have hpt : ∀ x, max (x - T) 0 + v + (T - v) * Set.indicator {x : ℝ | T ≤ x} 1 x ≤ max x v := by
    intro x
    by_cases hx : T ≤ x
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | T ≤ x} from hx),
        max_eq_left (show (0 : ℝ) ≤ x - T by linarith)]
      simp only [Pi.one_apply, mul_one]
      have := le_max_left x v
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | T ≤ x} from hx),
        max_eq_right (show x - T ≤ (0 : ℝ) by push_neg at hx; linarith)]
      simp only [mul_zero, add_zero, zero_add]
      exact le_max_right x v
  have hlhs : Integrable
      (fun x => max (x - T) 0 + v + (T - v) * Set.indicator {x : ℝ | T ≤ x} 1 x) μ :=
    ((int_sub_max μ hμ T).add (integrable_const v)).add hind
  have h1 := integral_mono hlhs (Aux_VR.int_max μ hμ v) hpt
  have hA : Integrable (fun x => max (x - T) 0 + v) μ :=
    (int_sub_max μ hμ T).add (integrable_const v)
  rw [integral_add hA hind,
    integral_add (int_sub_max μ hμ T) (integrable_const v), integral_const_mul,
    integral_indicator_one hs] at h1
  simpa [Measure.real] using h1

lemma prod_bounds {n : ℕ} (p : Fin n → ℝ) (hp : ∀ s, 0 ≤ p s ∧ p s ≤ 1) :
    ∀ L : List (Fin n), 0 ≤ (L.map p).prod ∧ (L.map p).prod ≤ 1 := by
  intro L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_nonneg (hp s).1 ih.1, mul_le_one₀ (hp s).2 ih.1 ih.2⟩

theorem prophet_list {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (T : ℝ) :
    ∀ L : List (Fin n),
      T * (1 - (L.map fun s => 1 - (ν s {x | T ≤ x}).toReal).prod) +
        (L.map fun s => 1 - (ν s {x | T ≤ x}).toReal).prod *
          (L.map fun s => ∫ x, max (x - T) 0 ∂(ν s)).sum ≤
        L.foldr (fun s v => ∫ x, max x v ∂(ν s)) 0 := by
  have hp : ∀ s, 0 ≤ 1 - (ν s {x | T ≤ x}).toReal ∧ 1 - (ν s {x | T ≤ x}).toReal ≤ 1 := by
    intro s
    haveI := hP s
    have h1 : (ν s {x | T ≤ x}).toReal ≤ 1 := by
      have := prob_le_one (μ := ν s) (s := {x | T ≤ x})
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h0 : 0 ≤ (ν s {x | T ≤ x}).toReal := ENNReal.toReal_nonneg
    constructor <;> linarith
  intro L
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.foldr_cons]
    haveI := hP s
    set p := 1 - (ν s {x | T ≤ x}).toReal with hpdef
    set P := (L.map fun s => 1 - (ν s {x | T ≤ x}).toReal).prod with hPdef
    set S := (L.map fun s => ∫ x, max (x - T) 0 ∂(ν s)).sum with hSdef
    set v := L.foldr (fun s v => ∫ x, max x v ∂(ν s)) 0 with hvdef
    set e := ∫ x, max (x - T) 0 ∂(ν s) with hedef
    have hstep := step_lb (ν s) (hint s) T v
    rw [← hedef] at hstep
    have hpb := hp s
    have hPb := prod_bounds _ hp L
    rw [← hPdef] at hPb
    have he0 : 0 ≤ e := integral_nonneg (fun x => le_max_right _ _)
    have hq : (ν s {x | T ≤ x}).toReal = 1 - p := by rw [hpdef]; ring
    rw [hq] at hstep
    -- hstep : e + v + (T - v) * (1 - p) ≤ ∫ max
    have h1 : p * (T * (1 - P) + P * S) ≤ p * v := mul_le_mul_of_nonneg_left ih hpb.1
    have h2 : p * P * e ≤ e := by
      have : p * P ≤ 1 := mul_le_one₀ hpb.2 hPb.1 hPb.2
      have h0 : 0 ≤ p * P := mul_nonneg hpb.1 hPb.1
      nlinarith
    nlinarith

lemma sup_le_sum {n : ℕ} (T : ℝ) (y : Fin n → ℝ) (hT : 0 ≤ T) :
    ⨆ i, y i ≤ T + ∑ i, max (y i - T) 0 := by
  have hs : 0 ≤ ∑ i, max (y i - T) 0 := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [Real.iSup_of_isEmpty]; linarith
  · apply ciSup_le
    intro i
    have : max (y i - T) 0 ≤ ∑ i, max (y i - T) 0 :=
      Finset.single_le_sum (f := fun i => max (y i - T) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_univ i)
    have := le_max_left (y i - T) 0
    linarith

lemma sup_abs_le {n : ℕ} (y : Fin n → ℝ) : |⨆ i, y i| ≤ ∑ i, |y i| := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [Real.iSup_of_isEmpty]; simp
  · have i0 : Fin n := h.some
    have hbdd : BddAbove (Set.range y) := Set.finite_range y |>.bddAbove
    have hs : ∀ i, |y i| ≤ ∑ i, |y i| := fun i =>
      Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    rw [abs_le]
    constructor
    · have h1 : y i0 ≤ ⨆ i, y i := le_ciSup hbdd i0
      have h2 := neg_abs_le (y i0)
      linarith [hs i0]
    · apply ciSup_le
      intro i
      exact le_trans (le_abs_self _) (hs i)

lemma sup_integrable {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) :
    Integrable (fun y : Fin n → ℝ => ⨆ i, y i) (Measure.pi ν) := by
  haveI : ∀ i, IsProbabilityMeasure (ν i) := hP
  have hsum : Integrable (fun y : Fin n → ℝ => ∑ i, |y i|) (Measure.pi ν) := by
    apply integrable_finset_sum
    intro i _
    exact (integrable_eval (μ := ν) (hint i)).abs
  refine Integrable.mono' hsum ?_ ?_
  · exact (Measurable.iSup (fun i => measurable_pi_apply i)).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact sup_abs_le y

theorem prophet {n : ℕ} (ν : Fin n → Measure ℝ) (hP : ∀ i, IsProbabilityMeasure (ν i))
    (hint : ∀ i, Integrable id (ν i)) (hM0 : 0 ≤ ∫ y, ⨆ i, y i ∂(Measure.pi ν)) :
    (∫ y, ⨆ i, y i ∂(Measure.pi ν)) / 2 ≤ Aux_VR.Rv ν 0 := by
  haveI : ∀ i, IsProbabilityMeasure (ν i) := hP
  set M := ∫ y, ⨆ i, y i ∂(Measure.pi ν) with hM
  set T := M / 2 with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have hL := prophet_list ν hP hint T (List.finRange n)
  have hRv : Aux_VR.Rv ν 0 = (List.finRange n).foldr (fun s v => ∫ x, max x v ∂(ν s)) 0 := by
    unfold Aux_VR.Rv; simp
  rw [hRv]
  set P := ((List.finRange n).map fun s => 1 - (ν s {x | T ≤ x}).toReal).prod with hPdef
  have hS : ((List.finRange n).map fun s => ∫ x, max (x - T) 0 ∂(ν s)).sum =
      ∑ s, ∫ x, max (x - T) 0 ∂(ν s) := (Fin.sum_univ_def _).symm
  rw [hS] at hL
  have hMle : M ≤ T + ∑ s, ∫ x, max (x - T) 0 ∂(ν s) := by
    have hint2 : Integrable (fun y : Fin n → ℝ => T + ∑ i, max (y i - T) 0) (Measure.pi ν) := by
      refine (integrable_const T).add (integrable_finset_sum _ (fun i _ => ?_))
      haveI := hP i
      exact integrable_comp_eval (μ := ν) (int_sub_max (ν i) (hint i) T)
    have h1 := integral_mono (sup_integrable ν hP hint) hint2 (fun y => sup_le_sum T y hT0)
    rw [integral_add (integrable_const T) (integrable_finset_sum _ (fun i _ => by
      haveI := hP i
      exact integrable_comp_eval (μ := ν) (int_sub_max (ν i) (hint i) T))),
      integral_finset_sum _ (fun i _ => by
        haveI := hP i
        exact integrable_comp_eval (μ := ν) (int_sub_max (ν i) (hint i) T))] at h1
    have h2 : ∀ i, ∫ y : Fin n → ℝ, max (y i - T) 0 ∂(Measure.pi ν) =
        ∫ x, max (x - T) 0 ∂(ν i) := by
      intro i
      haveI : ∀ i, IsProbabilityMeasure (ν i) := hP
      exact integral_comp_eval (μ := ν)
        (((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable)
    simp only [h2] at h1
    haveI : ∀ i, IsProbabilityMeasure (ν i) := hP
    simpa using h1
  have hPb := prod_bounds (fun s => 1 - (ν s {x | T ≤ x}).toReal) (fun s => by
    haveI := hP s
    have h1 : (ν s {x | T ≤ x}).toReal ≤ 1 := by
      have := prob_le_one (μ := ν s) (s := {x | T ≤ x})
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h0 : 0 ≤ (ν s {x | T ≤ x}).toReal := ENNReal.toReal_nonneg
    constructor <;> linarith) (List.finRange n)
  rw [← hPdef] at hPb
  have h3 : P * (M - T) ≤ P * ∑ s, ∫ x, max (x - T) 0 ∂(ν s) :=
    mul_le_mul_of_nonneg_left (by linarith) hPb.1
  have h4 : M - T = T := by rw [hT]; ring
  rw [h4] at h3
  nlinarith

lemma ae_nonneg {n : ℕ} (I : Instance n) : ∀ᵐ x ∂(Measure.pi I.μ), ∀ i, 0 ≤ x i := by
  rw [ae_all_iff]
  intro i
  have hmp := measurePreserving_eval I.μ i
  have h0 : (Measure.pi I.μ) (Function.eval i ⁻¹' Set.Iio 0) = 0 := by
    rw [hmp.measure_preimage measurableSet_Iio.nullMeasurableSet]
    exact I.nonneg i
  rw [ae_iff]
  have : {a : Fin n → ℝ | ¬ 0 ≤ a i} = Function.eval i ⁻¹' Set.Iio 0 := by
    ext a; simp
  rw [this]; exact h0

lemma sup_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ ⨆ i, x i := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · rw [Real.iSup_of_isEmpty]
  · exact le_trans (hx h.some) (le_ciSup (Set.finite_range x).bddAbove h.some)

theorem main {n : ℕ} (I : Instance n) :
    (∀ σ, (∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ)) / 2 ≤ V I σ) ∧
    OPT I ≤ ∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ) ∧
    (∀ σ, OPT I ≤ 2 * V I σ) ∧
    ∀ (σ₀ : Equiv.Perm (Fin n)) (ϵ : ℝ), 0 < ϵ → ϵ ≤ 1 →
      ∃ k : ℕ, k ≤ ⌈Real.log 2 / Real.log (1 + ϵ)⌉₊ ∧
        (1 - ϵ) * OPT I ≤ V I σ₀ * (1 + ϵ) ^ k ∧ V I σ₀ * (1 + ϵ) ^ k ≤ OPT I := by
  set M := ∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ) with hM
  have hM0 : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_nonneg I] with x hx
    exact sup_nonneg x hx
  -- reindexing
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      M = ∫ y, ⨆ i, y i ∂(Measure.pi fun i => I.μ (σ i)) := by
    intro σ
    have hmp := (measurePreserving_piCongrLeft I.μ σ).symm
    calc M = ∫ x, ⨆ i, ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ).symm x) i
          ∂(Measure.pi I.μ) := by
          rw [hM]; congr 1; funext x; exact (Equiv.iSup_comp (g := x) σ).symm
      _ = _ := hmp.integral_comp' (fun y : Fin n → ℝ => ⨆ i, y i)
  have h1 : ∀ σ, M / 2 ≤ V I σ := by
    intro σ
    rw [Aux_VR.V_eq_R]
    have hP : ∀ i, IsProbabilityMeasure ((fun i => I.μ (σ i)) i) := fun i => I.prob (σ i)
    have hint : ∀ i, Integrable id ((fun i => I.μ (σ i)) i) := fun i => I.integrable (σ i)
    have := prophet (fun i => I.μ (σ i)) hP hint (by rw [← hperm σ]; exact hM0)
    rw [← hperm σ] at this
    exact this
  have hVle : ∀ σ, V I σ ≤ M := by
    intro σ
    unfold V
    haveI : Nonempty (StoppingRule n) := ⟨Aux_VR.thr I σ⟩
    apply ciSup_le
    intro τ
    have hintR : Integrable (reward τ σ) (Measure.pi I.μ) := by
      have hmp := (measurePreserving_piCongrLeft I.μ σ).symm
      have h0 := Aux_VR.reward_integrable (fun i => I.μ (σ i)) (fun i => I.prob (σ i))
        (fun i => I.integrable (σ i)) τ
      exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h0
    refine integral_mono_ae hintR (sup_integrable I.μ (fun i => I.prob i) I.integrable) ?_
    filter_upwards [ae_nonneg I] with x hx
    unfold reward
    split
    · exact le_ciSup (Set.finite_range x).bddAbove _
    · exact sup_nonneg x hx
  have h2 : OPT I ≤ M := by
    unfold OPT
    exact Finset.sup'_le _ _ (fun σ _ => hVle σ)
  have hVopt : ∀ σ, V I σ ≤ OPT I := fun σ => by
    unfold OPT; exact Finset.le_sup' (V I) (Finset.mem_univ σ)
  have h3 : ∀ σ, OPT I ≤ 2 * V I σ := fun σ => by have := h1 σ; linarith
  refine ⟨h1, h2, h3, ?_⟩
  intro σ₀ ϵ hϵ0 hϵ1
  set v := V I σ₀ with hv
  have hv0 : 0 ≤ v := by
    rw [hv, Aux_VR.V_eq_R]; unfold Aux_VR.Rv
    exact Aux_VR.Rv_nonneg _ (fun i => I.prob (σ₀ i)) (fun i => I.integrable (σ₀ i)) _
  have hvO := hVopt σ₀
  have hO2 := h3 σ₀
  have hO0 : 0 ≤ OPT I := le_trans hv0 hvO
  set K := ⌈Real.log 2 / Real.log (1 + ϵ)⌉₊ with hK
  have hpow : 2 ≤ (1 + ϵ) ^ K := by
    have hl : 0 < Real.log (1 + ϵ) := Real.log_pos (by linarith)
    have hK1 : Real.log 2 / Real.log (1 + ϵ) ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ hl] at hK1
    have : Real.log 2 ≤ Real.log ((1 + ϵ) ^ K) := by rw [Real.log_pow]; linarith
    exact (Real.log_le_log_iff (by norm_num) (by positivity)).1 this
  set k := Nat.findGreatest (fun k => v * (1 + ϵ) ^ k ≤ OPT I) K with hk
  have hPk : v * (1 + ϵ) ^ k ≤ OPT I := by
    rw [hk]
    exact Nat.findGreatest_spec (P := fun k => v * (1 + ϵ) ^ k ≤ OPT I) (Nat.zero_le K)
      (by simpa using hvO)
  have hkK : k ≤ K := Nat.findGreatest_le K
  refine ⟨k, hkK, ?_, hPk⟩
  rcases Nat.lt_or_ge k K with hlt | hge
  · have hnot : ¬ (v * (1 + ϵ) ^ (k + 1) ≤ OPT I) :=
      Nat.findGreatest_is_greatest (P := fun k => v * (1 + ϵ) ^ k ≤ OPT I)
        (Nat.lt_succ_self k) (by omega)
    push_neg at hnot
    rw [pow_succ] at hnot
    have hp0 : 0 ≤ v * (1 + ϵ) ^ k := by positivity
    nlinarith
  · have hkeq : k = K := le_antisymm hkK hge
    rw [hkeq]
    have : 2 * v ≤ v * (1 + ϵ) ^ K := by nlinarith
    nlinarith

end Aux_EST

open FreeOrderEPTAS in
theorem solution {n : ℕ} (I : Instance n) :
    (∀ σ, (∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ)) / 2 ≤ V I σ) ∧
    OPT I ≤ ∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ) ∧
    (∀ σ, OPT I ≤ 2 * V I σ) ∧
    ∀ (σ₀ : Equiv.Perm (Fin n)) (ϵ : ℝ), 0 < ϵ → ϵ ≤ 1 →
      ∃ k : ℕ, k ≤ ⌈Real.log 2 / Real.log (1 + ϵ)⌉₊ ∧
        (1 - ϵ) * OPT I ≤ V I σ₀ * (1 + ϵ) ^ k ∧ V I σ₀ * (1 + ϵ) ^ k ≤ OPT I :=
  Aux_EST.main I
