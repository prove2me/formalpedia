-- Prove2me | solution 1 for ComputationalLearning.chernoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:57:30.862179+00:00
-- url     : https://prove2.me/submissions/1bed976f-2f96-401f-9168-e62cc7d250ce

import Mathlib
import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

section ChernoffProof

/-- A function with nonnegative derivative on `(0, a)` that vanishes at `0` is nonnegative
at `a`. -/
lemma ch_nonneg_of_deriv {f f' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (h0 : f 0 = 0)
    (hd : ∀ x ∈ Set.Icc 0 a, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo 0 a, 0 ≤ f' x) :
    0 ≤ f a := by
  have hcont : ContinuousOn f (Set.Icc 0 a) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x (Set.Ioo_subset_Icc_self hx)).deriv]
      exact hpos x hx
  have := hmono (Set.left_mem_Icc.mpr ha) (Set.right_mem_Icc.mpr ha) ha
  rw [h0] at this
  exact this

/-- `log (1 + x) ≥ 2x / (2 + x)` for `x ≥ 0`. -/
lemma ch_log_ge (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  have key := ch_nonneg_of_deriv (f := fun y => Real.log (1 + y) - 2 * y / (2 + y))
    (f' := fun y => y ^ 2 / ((1 + y) * (2 + y) ^ 2)) hx (by simp)
    (fun y hy => by
      have h1 : (1 + y) ≠ 0 := by linarith [hy.1]
      have h2 : (2 + y) ≠ 0 := by linarith [hy.1]
      have hl := ((hasDerivAt_id' y).const_add 1).log h1
      have hq := ((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 2) h2
      have hd : HasDerivAt (fun y => Real.log (1 + y) - 2 * y / (2 + y)) _ y := hl.sub hq
      refine hd.congr_deriv ?_
      field_simp
      ring)
    (fun y hy => by have := hy.1; positivity)
  linarith

/-- `(1 + γ) log (1 + γ) - γ ≥ γ² / 3` for `0 ≤ γ ≤ 1`. -/
lemma ch_upper_ineq (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    γ ^ 2 / 3 ≤ (1 + γ) * Real.log (1 + γ) - γ := by
  have hl := ch_log_ge γ h0
  have h2 : 0 < 2 + γ := by linarith
  have hmul : (1 + γ) * (2 * γ / (2 + γ)) ≤ (1 + γ) * Real.log (1 + γ) :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  have hid : (1 + γ) * (2 * γ / (2 + γ)) - γ = γ ^ 2 / (2 + γ) := by
    field_simp
    ring
  have hfrac : γ ^ 2 / 3 ≤ γ ^ 2 / (2 + γ) :=
    div_le_div_of_nonneg_left (sq_nonneg γ) h2 (by linarith)
  linarith

/-- `(1 - γ) log (1 - γ) + γ ≥ γ² / 2` for `0 ≤ γ < 1`. -/
lemma ch_lower_ineq (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) :
    γ ^ 2 / 2 ≤ (1 - γ) * Real.log (1 - γ) + γ := by
  have key := ch_nonneg_of_deriv (f := fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2)
    (f' := fun y => -Real.log (1 - y) - y) h0 (by simp)
    (fun y hy => by
      have h1' : (1 - y) ≠ 0 := by linarith [hy.2]
      have hs := (hasDerivAt_id' y).const_sub 1
      have hl := hs.log h1'
      have hp := (hs.mul hl).add (hasDerivAt_id' y)
      have hq : HasDerivAt (fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2) _ y :=
        hp.sub ((hasDerivAt_pow 2 y).div_const 2)
      refine hq.congr_deriv ?_
      field_simp
      ring)
    (fun y hy => by
      have hpos : 0 < 1 - y := by linarith [hy.2]
      have := Real.log_le_sub_one_of_pos hpos
      linarith)
  linarith

lemma ch_bern_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p) := by
  constructor
  rw [bernoulliMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hp0 (sub_nonneg.2 hp1)]
  simp

lemma ch_bern_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(bernoulliMeasure p) = p * f true + (1 - p) * f false := by
  unfold bernoulliMeasure
  rw [integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
      (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0,
    ENNReal.toReal_ofReal (sub_nonneg.2 hp1), smul_eq_mul, smul_eq_mul]

lemma ch_trials_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    IsProbabilityMeasure (trialsLaw p m) := by
  have := ch_bern_prob hp0 hp1
  unfold trialsLaw
  infer_instance

lemma ch_succ {m : ℕ} (ω : Fin m → Bool) :
    (successes ω : ℝ) = ∑ i, (if ω i = true then (1:ℝ) else 0) := by
  simp only [successes, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma ch_mgf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (t : ℝ) :
    mgf (fun ω : Fin m → Bool => (successes ω : ℝ)) (trialsLaw p m) t
      ≤ Real.exp (m * p * (Real.exp t - 1)) := by
  have := ch_bern_prob hp0 hp1
  have e : ∀ ω : Fin m → Bool, Real.exp (t * (successes ω : ℝ)) =
      ∏ i, Real.exp (t * (if ω i = true then (1:ℝ) else 0)) := by
    intro ω
    rw [ch_succ, Finset.mul_sum, Real.exp_sum]
  have hb : ∫ b, Real.exp (t * (if b = true then (1:ℝ) else 0)) ∂(bernoulliMeasure p)
      = 1 + p * (Real.exp t - 1) := by
    rw [ch_bern_integral hp0 hp1]
    simp
    ring
  unfold mgf
  simp_rw [e]
  unfold trialsLaw
  rw [integral_fintype_prod_eq_prod
    (fun (_ : Fin m) (b : Bool) => Real.exp (t * (if b = true then (1:ℝ) else 0)))]
  simp_rw [hb]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : 0 ≤ 1 + p * (Real.exp t - 1) := by
    have := mul_nonneg hp0 (Real.exp_pos t).le
    nlinarith
  calc (1 + p * (Real.exp t - 1)) ^ m ≤ (Real.exp (p * (Real.exp t - 1))) ^ m :=
        pow_le_pow_left₀ h1 (by linarith [Real.add_one_le_exp (p * (Real.exp t - 1))]) m
    _ = Real.exp (m * p * (Real.exp t - 1)) := by
        rw [← Real.exp_nat_mul]; ring_nf

lemma ch_upper_tail {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (a t : ℝ) (ht : 0 ≤ t) :
    (trialsLaw p m).real {ω | a ≤ (successes ω : ℝ)}
      ≤ Real.exp (-t * a + m * p * (Real.exp t - 1)) := by
  have := ch_trials_prob hp0 hp1 m
  have h := measure_ge_le_exp_mul_mgf (X := fun ω : Fin m → Bool => (successes ω : ℝ))
    (μ := trialsLaw p m) a ht Integrable.of_finite
  calc _ ≤ Real.exp (-t * a) * mgf (fun ω : Fin m → Bool => (successes ω : ℝ)) (trialsLaw p m) t := h
    _ ≤ Real.exp (-t * a) * Real.exp (m * p * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left (ch_mgf hp0 hp1 m t) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

lemma ch_lower_tail {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (a t : ℝ) (ht : t ≤ 0) :
    (trialsLaw p m).real {ω | (successes ω : ℝ) ≤ a}
      ≤ Real.exp (-t * a + m * p * (Real.exp t - 1)) := by
  have := ch_trials_prob hp0 hp1 m
  have h := measure_le_le_exp_mul_mgf (X := fun ω : Fin m → Bool => (successes ω : ℝ))
    (μ := trialsLaw p m) a ht Integrable.of_finite
  calc _ ≤ Real.exp (-t * a) * mgf (fun ω : Fin m → Bool => (successes ω : ℝ)) (trialsLaw p m) t := h
    _ ≤ Real.exp (-t * a) * Real.exp (m * p * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left (ch_mgf hp0 hp1 m t) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

/-- Hoeffding's inequality for a `[0, 1]`-valued function of the trials. -/
lemma ch_hoeff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (g : Bool → ℝ)
    (hg01 : ∀ b, g b ∈ Set.Icc (0:ℝ) 1) (t : ℝ) (ht : 0 ≤ t) :
    (trialsLaw p m).real {ω | t ≤ ∑ i : Fin m, (g (ω i) - ∫ b, g b ∂(bernoulliMeasure p))} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal))) := by
  have := ch_bern_prob hp0 hp1
  have := ch_trials_prob hp0 hp1 m
  set μg := ∫ b, g b ∂(bernoulliMeasure p) with hμg
  have hg : Measurable g := measurable_of_finite g
  have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → Bool) => g (ω i) - μg) (trialsLaw p m) := by
    unfold trialsLaw
    exact iIndepFun_pi (X := fun _ b => g b - μg) (fun _ => (hg.sub_const μg).aemeasurable)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasSubgaussianMGF
      (fun ω : Fin m → Bool => g (ω i) - μg) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) (trialsLaw p m) := by
    intro i _
    have hm : AEMeasurable (fun ω : Fin m → Bool => g (ω i)) (trialsLaw p m) :=
      (hg.comp (measurable_pi_apply i)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (a := 0) (b := 1) hm
      (Filter.Eventually.of_forall fun ω => hg01 (ω i))
    have hint : ∫ ω, g (ω i) ∂(trialsLaw p m) = μg := by
      unfold trialsLaw
      exact integral_comp_eval hg.aestronglyMeasurable
    rw [hint] at h
    exact h
  exact HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht

lemma ch_hoeff' {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (hm : 0 < m) (g : Bool → ℝ)
    (hg01 : ∀ b, g b ∈ Set.Icc (0:ℝ) 1) (γ : ℝ) (hγ : 0 ≤ γ) :
    (trialsLaw p m).real {ω | γ * m ≤ ∑ i : Fin m, (g (ω i) - ∫ b, g b ∂(bernoulliMeasure p))} ≤
      Real.exp (-(2 * m * γ ^ 2)) := by
  have h := ch_hoeff hp0 hp1 m g hg01 (γ * m) (mul_nonneg hγ (Nat.cast_nonneg m))
  refine h.trans (le_of_eq ?_)
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : ((∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = m / 4 := by
    push_cast
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  rw [hs]
  field_simp
  ring

lemma ch_toENN {m : ℕ} (μ : Measure (Fin m → Bool)) [IsFiniteMeasure μ]
    (s : Set (Fin m → Bool)) (b : ℝ) (h : μ.real s ≤ b) : μ s ≤ ENNReal.ofReal b := by
  rw [← ofReal_measureReal (measure_ne_top μ s)]
  exact ENNReal.ofReal_le_ofReal h

theorem ch_main {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    trialsLaw p m {ω | (p + γ) * m ≤ successes ω} ≤ ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (p - γ) * m} ≤
      ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (1 + γ) * p * m ≤ successes ω} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 3))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (1 - γ) * p * m} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 2))) := by
  have := ch_bern_prob hp0 hp1
  have := ch_trials_prob hp0 hp1 m
  have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg m) hp0
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- additive upper tail
    apply ch_toENN
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero]
      exact measureReal_le_one
    · set g : Bool → ℝ := fun b => if b = true then 1 else 0 with hg
      have hg01 : ∀ b, g b ∈ Set.Icc (0:ℝ) 1 := by
        intro b; cases b <;> simp [hg]
      have hE : ∫ b, g b ∂(bernoulliMeasure p) = p := by
        rw [ch_bern_integral hp0 hp1]; simp [hg]
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
        (ch_hoeff' hp0 hp1 m hm g hg01 γ hγ.le)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hE, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have := ch_succ ω
      simp only [hg]
      linarith
  · -- additive lower tail
    apply ch_toENN
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero]
      exact measureReal_le_one
    · set g : Bool → ℝ := fun b => if b = true then 0 else 1 with hg
      have hg01 : ∀ b, g b ∈ Set.Icc (0:ℝ) 1 := by
        intro b; cases b <;> simp [hg]
      have hE : ∫ b, g b ∂(bernoulliMeasure p) = 1 - p := by
        rw [ch_bern_integral hp0 hp1]; simp [hg]
      refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
        (ch_hoeff' hp0 hp1 m hm g hg01 γ hγ.le)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hE, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hs := ch_succ ω
      have hc : ∑ i, g (ω i) = m - ∑ i, (if ω i = true then (1:ℝ) else 0) := by
        rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
        rw [show (m : ℝ) = ∑ _i : Fin m, (1:ℝ) by simp]
        refine Finset.sum_congr rfl fun i _ => ?_
        cases ω i <;> simp [hg]
      rw [hc]
      linarith
  · -- multiplicative upper tail
    apply ch_toENN
    have h1γ : 0 < 1 + γ := by linarith
    have ht : 0 ≤ Real.log (1 + γ) := Real.log_nonneg (by linarith)
    refine (ch_upper_tail hp0 hp1 m _ _ ht).trans (Real.exp_le_exp.mpr ?_)
    rw [Real.exp_log h1γ]
    have hk := mul_le_mul_of_nonneg_left (ch_upper_ineq γ hγ.le hγ1) hmp
    nlinarith [hk]
  · -- multiplicative lower tail
    apply ch_toENN
    rcases lt_or_eq_of_le hγ1 with hlt | heq
    · have h1γ : 0 < 1 - γ := by linarith
      have ht : Real.log (1 - γ) ≤ 0 := Real.log_nonpos h1γ.le (by linarith)
      refine (ch_lower_tail hp0 hp1 m _ _ ht).trans (Real.exp_le_exp.mpr ?_)
      rw [Real.exp_log h1γ]
      have hk := mul_le_mul_of_nonneg_left (ch_lower_ineq γ hγ.le hlt) hmp
      nlinarith [hk]
    · subst heq
      have ht : -Real.log 2 ≤ 0 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
      refine (ch_lower_tail hp0 hp1 m _ _ ht).trans (Real.exp_le_exp.mpr ?_)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      nlinarith [hmp]

end ChernoffProof

end ComputationalLearning

open ComputationalLearning

theorem solution {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    trialsLaw p m {ω | (p + γ) * m ≤ successes ω} ≤ ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (p - γ) * m} ≤
      ENNReal.ofReal (Real.exp (-(2 * m * γ ^ 2))) ∧
    trialsLaw p m {ω | (1 + γ) * p * m ≤ successes ω} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 3))) ∧
    trialsLaw p m {ω | (successes ω : ℝ) ≤ (1 - γ) * p * m} ≤
      ENNReal.ofReal (Real.exp (-(m * p * γ ^ 2 / 2))) := by
  exact ch_main hp0 hp1 m hγ hγ1
