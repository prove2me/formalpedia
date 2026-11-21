-- Prove2me | solution 1 for FreeOrderEPTAS.value_eq_recursion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:11:20.331174+00:00
-- url     : https://prove2.me/submissions/da276b93-3694-453a-be5a-4da624422b56

import Mathlib
import Definitions.Def_FreeOrderEPTAS_V
import Definitions.Def_FreeOrderEPTAS_thresholdRule
import Definitions.Def_FreeOrderEPTAS_freeOrder

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

/-! ### the cost-accounting program -/

lemma pmf_pure_bind {α β : Type} (y : α) (k : α → PMF β) : (PMF.pure y >>= k) = k y :=
  pure_bind y k

lemma fold_run_gen {n : ℕ} (F : ℝ → Fin n → Prog ℝ) (g : ℝ → Fin n → ℝ)
    (hF : ∀ v t c, (F v t).run c =
      PMF.pure (g v t, ⟨c.ops + 1, c.oracle + 1, c.lpCalls, c.rndCalls, c.maxSize⟩))
    (l : List (Fin n)) :
    ∀ (b : ℝ) (c : Cost), (foldP l F b).run c =
      PMF.pure (l.foldl g b,
        ⟨c.ops + 2 * l.length, c.oracle + l.length, c.lpCalls, c.rndCalls, c.maxSize⟩) := by
  induction l with
  | nil =>
    intro b c
    cases c
    simp [foldP] <;> rfl
  | cons a l ih =>
    intro b c
    simp only [foldP, tick, StateT.run_bind, StateT.run_modify, pure_bind]
    rw [hF, pmf_pure_bind, ih]
    simp only [List.foldl_cons, List.length_cons]
    congr 3
    all_goals first | rfl | (dsimp only; ring) | omega

lemma step_run {n : ℕ} (o : Fin n → ℝ → ℝ) (σ : Equiv.Perm (Fin n)) (v : ℝ) (t : Fin n)
    (c : Cost) :
    (do
      let j ← opn 1 (σ t)
      callOrc o j v : Prog ℝ).run c =
      PMF.pure (o (σ t) v, ⟨c.ops + 1, c.oracle + 1, c.lpCalls, c.rndCalls, c.maxSize⟩) := by
  simp only [opn, tick, callOrc, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
    bind_assoc]
  rfl

theorem main {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    V I σ = R I σ 0 ∧
      ∫ x, reward (thresholdRule I σ) σ x ∂(Measure.pi I.μ) = R I σ 0 ∧
      ∀ r ∈ ((recursionP (orc I) σ).run 0).support, r.1 = R I σ 0 ∧ r.2.total ≤ 3 * n := by
  set ν : Fin n → Measure ℝ := fun i => I.μ (σ i) with hν
  have hP : ∀ i, IsProbabilityMeasure (ν i) := fun i => I.prob (σ i)
  have hint : ∀ i, Integrable id (ν i) := fun i => I.integrable (σ i)
  have hR : ∀ t, R I σ t = Rv ν t := fun t => rfl
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
  have hle : ∀ τ : StoppingRule n, ∫ x, reward τ σ x ∂(Measure.pi I.μ) ≤ R I σ 0 := by
    intro τ
    rw [hint_eq, hR]
    exact bound n ν hP hint τ
  have heq : ∫ x, reward (thresholdRule I σ) σ x ∂(Measure.pi I.μ) = R I σ 0 := by
    rw [hint_eq, hR]
    exact attained n ν hP hint _ (fun t obs => rfl)
  refine ⟨?_, heq, ?_⟩
  · unfold V
    haveI : Nonempty (StoppingRule n) := ⟨thresholdRule I σ⟩
    apply le_antisymm
    · exact ciSup_le hle
    · rw [← heq]
      exact le_ciSup ⟨R I σ 0, by rintro _ ⟨τ, rfl⟩; exact hle τ⟩ (thresholdRule I σ)
  · intro r hr
    unfold recursionP at hr
    rw [fold_run_gen _ (fun v t => orc I (σ t) v) (step_run (orc I) σ)
      (List.finRange n).reverse 0 0] at hr
    rw [PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    constructor
    · simp only [List.foldl_reverse]
      rfl
    · simp [Cost.total]
      show 0 + 2 * n + (0 + n) + 0 + 0 ≤ 3 * n
      omega

end Aux_VR

open FreeOrderEPTAS in
theorem solution {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    V I σ = R I σ 0 ∧
      ∫ x, reward (thresholdRule I σ) σ x ∂(Measure.pi I.μ) = R I σ 0 ∧
      ∀ r ∈ ((recursionP (orc I) σ).run 0).support, r.1 = R I σ 0 ∧ r.2.total ≤ 3 * n :=
  Aux_VR.main I σ
