-- Prove2me | solution 1 for ChenChaoShiSALA.Regret.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:48:22.575989+00:00
-- url     : https://prove2.me/submissions/a7b926ce-d150-48a2-9b64-64b5f4257da7

import Mathlib

open MeasureTheory ProbabilityTheory

namespace L1x

def sp (t : ℕ) : Prop := ∃ m : ℕ, 4 ≤ m ∧ t + 1 = 2 ^ m

open Classical in
noncomputable def pr (t : ℕ) : ℝ := if sp t then 4 / ((t : ℝ) + 1) ^ 4 else 0

noncomputable def am (t : ℕ) : ℝ := ((t : ℝ) + 1) ^ 2 / 2

open Classical in
noncomputable def fv (t : ℕ) : Fin 3 → ℝ := if sp t then ![0, am t, -am t] else fun _ => 0

noncomputable def nu (t : ℕ) : MeasureTheory.Measure (Fin 3) :=
  ENNReal.ofReal (1 - pr t) • Measure.dirac 0 + ENNReal.ofReal (pr t / 2) • Measure.dirac 1 +
    ENNReal.ofReal (pr t / 2) • Measure.dirac 2

lemma pr_nonneg (t : ℕ) : 0 ≤ pr t := by
  unfold pr; split_ifs
  · positivity
  · exact le_rfl

lemma pr_le_one (t : ℕ) : pr t ≤ 1 := by
  unfold pr; split_ifs with h
  · obtain ⟨m, hm, hmt⟩ := h
    have h16 : (16 : ℝ) ≤ (t : ℝ) + 1 := by
      have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have : (16 : ℕ) ≤ t + 1 := by omega
      exact_mod_cast this
    rw [div_le_one (by positivity)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16) h16 4]
  · exact zero_le_one

instance nu_prob (t : ℕ) : IsProbabilityMeasure (nu t) := by
  constructor
  have h1 := pr_nonneg t
  have h2 := pr_le_one t
  simp only [nu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith)]
  rw [show 1 - pr t + pr t / 2 + pr t / 2 = 1 by ring]
  simp

instance fin_sm (c : ℝ) (x : Fin 3) : IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac x) :=
  ⟨by simp [Measure.smul_apply]⟩

lemma nu_integral (t : ℕ) (g : Fin 3 → ℝ) :
    ∫ x, g x ∂(nu t) = (1 - pr t) * g 0 + pr t / 2 * g 1 + pr t / 2 * g 2 := by
  have h1 := pr_nonneg t
  have h2 := pr_le_one t
  unfold nu
  rw [integral_add_measure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - pr t),
      ENNReal.toReal_ofReal (by linarith : 0 ≤ pr t / 2), smul_eq_mul]
  all_goals exact Integrable.of_finite

abbrev Om := ℕ → Fin 3

noncomputable def mu : Measure Om := Measure.infinitePi nu

instance mu_prob : IsProbabilityMeasure mu := by unfold mu; infer_instance

lemma ev_integral (t : ℕ) (g : Fin 3 → ℝ) : ∫ ω, g (ω t) ∂mu = ∫ x, g x ∂(nu t) := by
  have := integral_map (μ := mu) (φ := fun ω : Om => ω t) (f := g)
    (measurable_pi_apply t).aemeasurable (Measurable.of_discrete).aestronglyMeasurable
  unfold mu at *
  rw [Measure.infinitePi_map_eval] at this
  exact this.symm

lemma ev_integrable (t : ℕ) (g : Fin 3 → ℝ) : Integrable (fun ω : Om => g (ω t)) mu := by
  have h : Integrable g (mu.map (fun ω : Om => ω t)) := by
    unfold mu; rw [Measure.infinitePi_map_eval]; exact Integrable.of_finite
  exact (integrable_map_measure (Measurable.of_discrete).aestronglyMeasurable
    (measurable_pi_apply t).aemeasurable).1 h

open Classical in
noncomputable def bb (s : ℕ) : ℝ := if sp s then am s else 0

lemma am_nonneg (s : ℕ) : 0 ≤ am s := by unfold am; positivity

lemma fv_bound (s : ℕ) (x : Fin 3) : |fv s x| ≤ bb s := by
  unfold fv bb
  split_ifs
  · fin_cases x <;> simp [abs_of_nonneg (am_nonneg s), am_nonneg s]
  · simp

lemma bb_nonneg (s : ℕ) : 0 ≤ bb s := by
  unfold bb; split_ifs
  · exact am_nonneg s
  · exact le_rfl

lemma bb_zero_between (m s : ℕ) (h1 : 2 ^ m ≤ s) (h2 : s + 1 < 2 ^ (m + 1)) : bb s = 0 := by
  unfold bb; rw [if_neg]
  rintro ⟨j, -, hj⟩
  have a : m < j := by
    by_contra hc
    have hc := not_lt.mp hc
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hc
    omega
  have : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) a
  omega

lemma Phi (m : ℕ) : ∑ s ∈ Finset.range (2 ^ m - 1), bb s ≤ (4 : ℝ) ^ m / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have e : 2 ^ (m + 1) - 1 = ((2 ^ m - 1) + 1) + (2 ^ m - 1) := by rw [pow_succ]; omega
    rw [e, Finset.sum_range_add, Finset.sum_range_succ]
    have hz : ∑ x ∈ Finset.range (2 ^ m - 1), bb ((2 ^ m - 1) + 1 + x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_range] at hx
      apply bb_zero_between m
      · omega
      · rw [pow_succ]; omega
    rw [hz]
    have hb : bb (2 ^ m - 1) ≤ (4 : ℝ) ^ m / 2 := by
      have hc : (((2 ^ m - 1 : ℕ) : ℝ) + 1) = 2 ^ m := by
        have := Nat.sub_add_cancel hpos
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
      unfold bb am
      split_ifs
      · rw [hc]
        have : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]
      · positivity
    have : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
    rw [this]
    linarith

lemma sqint (t : ℕ) : ∫ ω, (fv t (ω t)) ^ 2 ∂mu ≤ 1 := by
  rw [ev_integral t (fun x => (fv t x) ^ 2), nu_integral]
  unfold fv
  split_ifs with h
  · have hp : pr t = 4 / ((t : ℝ) + 1) ^ 4 := by unfold pr; rw [if_pos h]
    have hne : ((t : ℝ) + 1) ≠ 0 := by positivity
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hp, am]
    apply le_of_eq
    field_simp
    ring
  · simp

lemma mean_zero (t : ℕ) : ∫ ω, fv t (ω t) ∂mu = 0 := by
  rw [ev_integral t (fv t), nu_integral]
  unfold fv
  split_ifs with h
  · simp
  · simp

lemma prE (t : ℕ) : mu {ω | ω t ≠ 0} = ENNReal.ofReal (pr t) := by
  have h1 := pr_nonneg t
  have : mu {ω | ω t ≠ 0} = (mu.map (fun ω : Om => ω t)) {x | x ≠ 0} :=
    (Measure.map_apply (μ := mu) (measurable_pi_apply (δ := ℕ) (X := fun _ : ℕ => Fin 3) t)
      (s := {x : Fin 3 | x ≠ 0}) (MeasurableSet.of_discrete)).symm
  rw [this]
  unfold mu
  rw [Measure.infinitePi_map_eval]
  simp only [nu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
  simp
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  ring

lemma fv_big (t : ℕ) (h : sp t) (x : Fin 3) (hx : x ≠ 0) : |fv t x| = am t := by
  unfold fv; rw [if_pos h]
  fin_cases x
  · exact absurd rfl hx
  · simp [abs_of_nonneg (am_nonneg t)]
  · simp [abs_of_nonneg (am_nonneg t)]

lemma key (m : ℕ) (hm : 4 ≤ m) (ω : Om) (hω : ω (2 ^ m - 1) ≠ 0)
    (hS : |(∑ s ∈ Finset.range (2 ^ m), fv s (ω s)) / ((2 ^ m : ℕ) : ℝ)| ≤ 4) : False := by
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have ht : (2 ^ m - 1) + 1 = 2 ^ m := Nat.sub_add_cancel hpos
  have hsp : sp (2 ^ m - 1) := ⟨m, hm, ht⟩
  have hL16 : (16 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact_mod_cast (by omega : (16 : ℕ) ≤ 2 ^ m)
  set L : ℝ := ((2 ^ m : ℕ) : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hc : (((2 ^ m - 1 : ℕ) : ℝ) + 1) = L := by
    rw [hLdef, ← ht]; push_cast; ring
  have hsum : ∑ s ∈ Finset.range (2 ^ m), fv s (ω s) =
      ∑ s ∈ Finset.range (2 ^ m - 1), fv s (ω s) + fv (2 ^ m - 1) (ω (2 ^ m - 1)) := by
    conv_lhs => rw [← ht]
    exact Finset.sum_range_succ _ _
  have h1 : |∑ s ∈ Finset.range (2 ^ m - 1), fv s (ω s)| ≤ L ^ 2 / 6 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun s _ => fv_bound s (ω s))) ?_
    refine le_trans (Phi m) ?_
    have : (4 : ℝ) ^ m = L ^ 2 := by
      rw [hLdef]; push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
  have h2 : |fv (2 ^ m - 1) (ω (2 ^ m - 1))| = L ^ 2 / 2 := by
    rw [fv_big _ hsp _ hω]; unfold am; rw [hc]
  have h3 : L ^ 2 / 3 ≤ |∑ s ∈ Finset.range (2 ^ m), fv s (ω s)| := by
    rw [hsum]
    have := abs_sub_abs_le_abs_sub (fv (2 ^ m - 1) (ω (2 ^ m - 1)))
      (-(∑ s ∈ Finset.range (2 ^ m - 1), fv s (ω s)))
    rw [abs_neg, sub_neg_eq_add, add_comm] at this
    linarith
  rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos] at hS
  nlinarith

end L1x

open L1x in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ t, Measurable (X t)) (hi : iIndepFun X μ)
    (hint : ∀ t, Integrable (X t) μ)
    (hsq : ∀ t, Integrable (fun ω => (X t ω) ^ 2) μ)
    (hc : ∀ t, (∫ ω, X t ω ∂μ) = 0)
    (hmgf : ∃ rho : ℝ, 0 < rho ∧ ∀ t, ∀ s ∈ Set.Ioo (-rho) rho,
      Integrable (fun ω => Real.exp (s * X t ω)) μ),
    ∃ L0 : ℕ, 2 ≤ L0 ∧ ∀ L ≥ L0,
      (μ {ω | |(∑ t ∈ Finset.range L, X t ω) / (L : ℝ)| ≤
        4 * sSup {v : ℝ | ∃ t < L, v = Real.sqrt (∫ ω, (X t ω) ^ 2 ∂μ)} *
          (L : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L)}).toReal >
        1 - 2 / (L : ℝ) ^ 4) := by
  intro H
  obtain ⟨L0, hL0, hL⟩ := H (Ω := Om) mu (fun t ω => fv t (ω t))
    (fun t => (Measurable.of_discrete).comp (measurable_pi_apply t))
    (by unfold mu; exact iIndepFun_infinitePi (P := nu) (X := fv) (fun t => Measurable.of_discrete))
    (fun t => ev_integrable t (fv t))
    (fun t => ev_integrable t (fun x => (fv t x) ^ 2))
    mean_zero
    ⟨1, one_pos, fun t s _ => ev_integrable t (fun x => Real.exp (s * fv t x))⟩
  set m : ℕ := max 4 L0 with hmdef
  have hm4 : 4 ≤ m := le_max_left _ _
  have hLge : L0 ≤ 2 ^ m := by
    have h1 : L0 ≤ m := le_max_right _ _
    have h2 : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  have h := hL (2 ^ m) hLge
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have ht : (2 ^ m - 1) + 1 = 2 ^ m := Nat.sub_add_cancel hpos
  have hL16 : (16 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    exact_mod_cast (by omega : (16 : ℕ) ≤ 2 ^ m)
  set L : ℝ := ((2 ^ m : ℕ) : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hc : (((2 ^ m - 1 : ℕ) : ℝ) + 1) = L := by
    rw [hLdef, ← ht]; push_cast; ring
  set G := {ω : Om | |(∑ t ∈ Finset.range (2 ^ m), fv t (ω t)) / L| ≤
        4 * sSup {v : ℝ | ∃ t < 2 ^ m, v = Real.sqrt (∫ ω, (fv t (ω t)) ^ 2 ∂mu)} *
          L ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L)} with hG
  have hsS : sSup {v : ℝ | ∃ t < 2 ^ m, v = Real.sqrt (∫ ω, (fv t (ω t)) ^ 2 ∂mu)} ≤ 1 := by
    apply Real.sSup_le _ (by norm_num)
    rintro v ⟨s, -, rfl⟩
    exact Real.sqrt_le_one.mpr (sqint s) |>.trans_eq rfl
  have hAB : L ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L) ≤ 1 := by
    rw [Real.rpow_neg hLpos.le, ← Real.sqrt_eq_rpow]
    have hsq : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
    rw [← div_eq_inv_mul, div_le_one hsq]
    apply Real.sqrt_le_sqrt
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hAnn : 0 ≤ L ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hLpos.le _
  have hBnn : 0 ≤ Real.sqrt (Real.log L) := Real.sqrt_nonneg _
  have hdisj : Disjoint G {ω : Om | ω (2 ^ m - 1) ≠ 0} := by
    rw [Set.disjoint_left]
    intro ω hω hE
    apply key m hm4 ω hE
    have : |(∑ t ∈ Finset.range (2 ^ m), fv t (ω t)) / L| ≤ 4 * 1 * L ^ (-(1 / 2 : ℝ)) *
        Real.sqrt (Real.log L) := by
      refine le_trans hω ?_
      have := mul_nonneg hAnn hBnn
      have h4 : 4 * sSup {v : ℝ | ∃ t < 2 ^ m, v = Real.sqrt (∫ ω, (fv t (ω t)) ^ 2 ∂mu)} ≤ 4 * 1 := by
        linarith
      calc _ = 4 * sSup {v : ℝ | ∃ t < 2 ^ m, v = Real.sqrt (∫ ω, (fv t (ω t)) ^ 2 ∂mu)} *
            (L ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L)) := by ring
        _ ≤ 4 * 1 * (L ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L)) :=
            mul_le_mul_of_nonneg_right h4 this
        _ = _ := by ring
    calc _ ≤ _ := this
      _ ≤ 4 * 1 * 1 := by
        have := mul_le_mul_of_nonneg_left hAB (by norm_num : (0:ℝ) ≤ 4 * 1)
        linarith
      _ = 4 := by norm_num
  have hEm : MeasurableSet {ω : Om | ω (2 ^ m - 1) ≠ 0} :=
    (measurable_pi_apply (δ := ℕ) (X := fun _ : ℕ => Fin 3) (2 ^ m - 1))
      (MeasurableSet.of_discrete : MeasurableSet {x : Fin 3 | x ≠ 0})
  have hU := measure_union hdisj hEm (μ := mu)
  have hle : mu (G ∪ {ω : Om | ω (2 ^ m - 1) ≠ 0}) ≤ 1 := prob_le_one
  rw [hU, prE] at hle
  have hp : pr (2 ^ m - 1) = 4 / L ^ 4 := by
    have hsp : sp (2 ^ m - 1) := ⟨m, hm4, ht⟩
    unfold pr; rw [if_pos hsp, hc]
  have hp0 := pr_nonneg (2 ^ m - 1)
  have hfin : mu G ≠ ⊤ := measure_ne_top _ _
  have h5 : (mu G).toReal + pr (2 ^ m - 1) ≤ 1 := by
    have := ENNReal.toReal_mono (by simp) hle
    rw [ENNReal.toReal_add hfin (by simp), ENNReal.toReal_ofReal hp0] at this
    simpa using this
  rw [hp] at h5
  have h6 : 2 / L ^ 4 < 4 / L ^ 4 := by
    apply div_lt_div_of_pos_right (by norm_num) (by positivity)
  have h7 : 1 - 2 / L ^ 4 < (mu G).toReal := h
  linarith
