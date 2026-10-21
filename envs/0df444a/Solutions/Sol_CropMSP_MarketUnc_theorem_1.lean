-- Prove2me | solution 1 for CropMSP.MarketUnc.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:23:58.435864+00:00
-- url     : https://prove2.me/submissions/a501df89-91cf-4fbe-99f8-72c3fb2caebe

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

set_option autoImplicit false
open MeasureTheory CropMSP.MarketUnc

theorem cm_lossProb (P : Params) (hθ : 0 < P.θ) (m q c : ℝ) (h : m ≤ c) :
    lossProb P m q c = max 0 (min P.θ (c - P.a + q) + P.θ) / (2 * P.θ) := by
  unfold lossProb effPrice price
  have hS : {ε ∈ Set.Icc (-P.θ) P.θ | max m (P.a - q + ε) ≤ c} =
      Set.Icc (-P.θ) (min P.θ (c - P.a + q)) := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h, by linarith⟩
  rw [hS, Real.volume_Icc, ENNReal.toReal_ofReal']
  rw [max_comm]
  congr 3
  ring

theorem cm_lossProb_lt (P : Params) (hθ : 0 < P.θ) (m q c : ℝ) (h : c < m) :
    lossProb P m q c = 0 := by
  unfold lossProb effPrice price
  have hS : {ε ∈ Set.Icc (-P.θ) P.θ | max m (P.a - q + ε) ≤ c} = ∅ := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, max_le_iff]
    intro _ h2
    linarith
  rw [hS]; simp

theorem cm_luc (P : Params) (hS : P.Standing) (m q c : ℝ) :
    Lucrative P m q c ↔ c < m ∨ (m ≤ c ∧ c ≤ P.a - q - (1 - 2 * P.α) * P.θ) := by
  obtain ⟨hα0, hα1, hθ, -, -⟩ := hS
  unfold Lucrative
  by_cases h : c < m
  · rw [cm_lossProb_lt P hθ m q c h]
    simp [h, hα0.le]
  · push_neg at h
    rw [cm_lossProb P hθ m q c h, div_le_iff₀ (by linarith)]
    have : ¬ c < m := not_lt.mpr h
    simp only [this, false_or, h, true_and]
    have h2 : (0:ℝ) ≤ P.α * (2 * P.θ) := by positivity
    rw [max_le_iff]
    constructor
    · rintro ⟨-, h3⟩
      by_contra hc
      push_neg at hc
      have : P.θ < min P.θ (c - P.a + q) + P.θ ∨ True := Or.inr trivial
      rcases le_total P.θ (c - P.a + q) with h4 | h4
      · rw [min_eq_left h4] at h3; nlinarith
      · rw [min_eq_right h4] at h3; nlinarith
    · intro h3
      refine ⟨h2, ?_⟩
      have := min_le_right P.θ (c - P.a + q)
      linarith

theorem cm_var_threshold (P : Params) (hS : P.Standing) (m q c : ℝ) :
    (c < m → Lucrative P m q c) ∧
    (m ≤ c → (Lucrative P m q c ↔ c ≤ P.a - q - (1 - 2 * P.α) * P.θ)) := by
  refine ⟨fun h => (cm_luc P hS m q c).2 (Or.inl h), fun h => ?_⟩
  rw [cm_luc P hS]
  constructor
  · rintro (h1 | ⟨-, h2⟩)
    · linarith
    · exact h2
  · intro h2; exact Or.inr ⟨h, h2⟩

theorem cm_tau0_gt (P : Params) (hS : P.Standing) : 1 / 2 < tau0 P := by
  obtain ⟨hα0, hα1, hθ, h1, -⟩ := hS
  unfold tau0
  nlinarith

theorem cm_tau_cases (P : Params) (hS : P.Standing) (m : ℝ) :
    (m ≤ tau0 P ∧ tau P m = tau0 P) ∨ (tau0 P < m ∧ m ≤ 1 ∧ tau P m = m) ∨
      (1 < m ∧ tau P m = 1) := by
  have h0 := cm_tau0_gt P hS
  have h1 := hS.2.2.2.2
  unfold tau
  rcases le_or_gt m (tau0 P) with h | h
  · left
    refine ⟨h, ?_⟩
    rw [max_eq_right h, min_eq_right h1.le]
  · right
    rcases le_or_gt m 1 with h' | h'
    · left
      refine ⟨h, h', ?_⟩
      rw [max_eq_left h.le, min_eq_right h']
    · right
      refine ⟨h', ?_⟩
      rw [max_eq_left h.le, min_eq_left h'.le]

theorem cm_tau_mem (P : Params) (hS : P.Standing) (m : ℝ) : tau P m ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := cm_tau0_gt P hS
  have h1 := hS.2.2.2.2
  rcases cm_tau_cases P hS m with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;> rw [e] <;> constructor <;> linarith

theorem cm_luc_tau (P : Params) (hS : P.Standing) (m c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hne : c ≠ tau P m) : Lucrative P m (tau P m) c ↔ c ≤ tau P m := by
  rw [cm_luc P hS]
  have hT : P.a - tau P m - (1 - 2 * P.α) * P.θ = 2 * tau0 P - tau P m := by
    unfold tau0; ring
  rw [hT]
  have h0 := cm_tau0_gt P hS
  obtain ⟨hc0, hc1⟩ := hc
  rcases cm_tau_cases P hS m with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩
  · rw [e] at hne ⊢
    constructor
    · rintro (h | ⟨h, h'⟩) <;> linarith
    · intro h
      rcases lt_or_ge c m with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', by linarith⟩
  · rw [e] at hne ⊢
    constructor
    · rintro (h | ⟨h, h'⟩)
      · linarith
      · linarith
    · intro h
      exact Or.inl (lt_of_le_of_ne h hne)
  · rw [e] at hne ⊢
    constructor
    · rintro (h | ⟨h, h'⟩) <;> linarith
    · intro h
      exact Or.inl (by linarith)

theorem cm_sowers_ae (P : Params) (hS : P.Standing) (m : ℝ) :
    sowers P m (tau P m) =ᵐ[volume] Set.Icc 0 (tau P m) := by
  have hne : ∀ᵐ c ∂(volume : Measure ℝ), c ≠ tau P m := by
    have := (Set.countable_singleton (tau P m)).ae_notMem (volume : Measure ℝ)
    simpa using this
  rw [Filter.eventuallyEq_set]
  filter_upwards [hne] with c hc
  have hτ := cm_tau_mem P hS m
  unfold sowers
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.1, (cm_luc_tau P hS m c ⟨h1.1, h1.2⟩ hc).1 h2⟩
  · rintro ⟨h1, h2⟩
    have hm : c ∈ Set.Icc (0 : ℝ) 1 := ⟨h1, h2.trans hτ.2⟩
    exact ⟨hm, (cm_luc_tau P hS m c hm hc).2 h2⟩

theorem cm_equil (P : Params) (hS : P.Standing) (m : ℝ) : IsEquilibrium P m (tau P m) := by
  refine ⟨cm_tau_mem P hS m, ?_⟩
  rw [measure_congr (cm_sowers_ae P hS m), Real.volume_Icc, ENNReal.toReal_ofReal]
  · ring
  · have := (cm_tau_mem P hS m).1
    linarith

theorem cm_sowers_anti (P : Params) (hS : P.Standing) (m q q' : ℝ) (h : q ≤ q') :
    sowers P m q' ⊆ sowers P m q := by
  intro c hc
  obtain ⟨h1, h2⟩ := hc
  refine ⟨h1, ?_⟩
  rw [cm_luc P hS] at h2 ⊢
  rcases h2 with h2 | ⟨h2, h3⟩
  · exact Or.inl h2
  · exact Or.inr ⟨h2, by linarith⟩

theorem cm_sowers_fin (P : Params) (m q : ℝ) : volume (sowers P m q) ≠ ⊤ := by
  have hsub : sowers P m q ⊆ Set.Icc (0 : ℝ) 1 := fun c hc => hc.1
  exact (lt_of_le_of_lt (measure_mono hsub) measure_Icc_lt_top).ne

theorem cm_unique (P : Params) (hS : P.Standing) (m q q' : ℝ) (h : IsEquilibrium P m q)
    (h' : IsEquilibrium P m q') : q = q' := by
  have key : ∀ x y, IsEquilibrium P m x → IsEquilibrium P m y → x ≤ y → y ≤ x := by
    intro x y hx hy hxy
    have := ENNReal.toReal_mono (cm_sowers_fin P m x)
      (measure_mono (cm_sowers_anti P hS m x y hxy))
    rw [hx.2, hy.2] at this
    exact this
  rcases le_total q q' with h1 | h1
  · exact le_antisymm h1 (key q q' h h' h1)
  · exact le_antisymm (key q' q h' h h1) h1

theorem cm_eq_tau (P : Params) (hS : P.Standing) (m q : ℝ) (h : IsEquilibrium P m q) :
    q = tau P m := cm_unique P hS m q _ h (cm_equil P hS m)

/-! ### integrals -/

theorem cm_cont (P : Params) (m q : ℝ) :
    Continuous (fun ε => max 0 (m - price P q ε)) := by
  unfold price; fun_prop

theorem cm_I1 (P : Params) (m q : ℝ) (hk1 : -P.θ ≤ m - P.a + q) (hk2 : m - P.a + q ≤ P.θ) :
    ∫ ε in (-P.θ)..P.θ, max 0 (m - price P q ε) = (m - P.a + q + P.θ) ^ 2 / 2 := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun ε => max 0 (m - price P q ε)) volume x y :=
    fun x y => (cm_cont P m q).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-P.θ) (m - P.a + q))
    (hint (m - P.a + q) P.θ)]
  have e1 : ∫ ε in (-P.θ)..(m - P.a + q), max 0 (m - price P q ε) =
      ∫ ε in (-P.θ)..(m - P.a + q), ((m - P.a + q) - ε) := by
    apply intervalIntegral.integral_congr
    intro ε hε
    rw [Set.uIcc_of_le hk1] at hε
    show max 0 (m - (P.a - q + ε)) = (m - P.a + q) - ε
    rw [max_eq_right (by linarith [hε.2])]
    ring
  have e2 : ∫ ε in (m - P.a + q)..P.θ, max 0 (m - price P q ε) =
      ∫ ε in (m - P.a + q)..P.θ, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro ε hε
    rw [Set.uIcc_of_le hk2] at hε
    show max 0 (m - (P.a - q + ε)) = 0
    rw [max_eq_left (by linarith [hε.1])]
  rw [e1, e2]
  simp only [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const, smul_eq_mul, mul_zero, add_zero]
  ring

theorem cm_I2 (P : Params) (m q : ℝ) (hk1 : -P.θ ≤ m - P.a + q) (hk2 : m - P.a + q ≤ P.θ) :
    ∫ ε in (-P.θ)..P.θ, effPrice P m q ε =
      2 * P.θ * (P.a - q) + (m - P.a + q + P.θ) ^ 2 / 2 := by
  have h1 : ∀ ε, effPrice P m q ε = price P q ε + max 0 (m - price P q ε) := by
    intro ε
    unfold effPrice
    rcases le_total m (price P q ε) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  simp_rw [h1]
  have hp : Continuous (fun ε => price P q ε) := by unfold price; fun_prop
  rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
    ((cm_cont P m q).intervalIntegrable _ _), cm_I1 P m q hk1 hk2]
  unfold price
  simp only [intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

theorem cm_eq11 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    expenditure P m q =
      tau P m / (4 * P.θ) * (m - (P.a - tau P m - P.θ)) ^ 2 := by
  have hq := cm_eq_tau P hS m q heq
  subst hq
  obtain ⟨h1, h2⟩ := hadm
  have hθ := hS.2.2.1
  unfold expenditure expEps
  beta_reduce
  rw [cm_I1 P m (tau P m) (by linarith) (by linarith)]
  field_simp
  ring

theorem cm_eq10 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    farmerSurplus P m q =
      tau P m / 4 *
        (((m - (P.a - tau P m) + P.θ) ^ 2) / P.θ + 2 * (2 * P.a - 3 * tau P m)) := by
  have hq := cm_eq_tau P hS m q heq
  subst hq
  obtain ⟨h1, h2⟩ := hadm
  have hθ := hS.2.2.1
  have hτ := cm_tau_mem P hS m
  unfold farmerSurplus
  rw [setIntegral_congr_set (cm_sowers_ae P hS m)]
  have hE : expEps P (fun ε => effPrice P m (tau P m) ε) =
      (2 * P.θ * (P.a - tau P m) + (m - P.a + tau P m + P.θ) ^ 2 / 2) / (2 * P.θ) := by
    unfold expEps
    rw [cm_I2 P m (tau P m) (by linarith) (by linarith)]
  rw [hE, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.1]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul, sub_zero]
  field_simp
  ring

theorem cm_eq12 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) :
    consumerSurplus P q = (tau P m) ^ 2 / 2 := by
  have hq := cm_eq_tau P hS m q heq
  rw [← hq]
  have hθ := hS.2.2.1
  have hin : ∀ ε, ∫ x in (0 : ℝ)..q, (price P x ε - price P q ε) = q ^ 2 / 2 := by
    intro ε
    unfold price
    have : (fun x : ℝ => P.a - x + ε - (P.a - q + ε)) = fun x => q - x := by
      funext x; ring
    rw [this, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul, sub_zero]
    ring
  unfold consumerSurplus expEps
  simp_rw [hin]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

theorem solution (P : Params) (hS : P.Standing) (m : ℝ)
    (hAdm : Admissible P m (tau P m)) :
    IsEquilibrium P m (tau P m) ∧
    (∀ q, IsEquilibrium P m q → q = tau P m) ∧
    (∀ c ∈ Set.Icc (0 : ℝ) 1, c ≠ tau P m →
      (Lucrative P m (tau P m) c ↔ c ≤ tau P m)) ∧
    (∀ m' : ℝ, Admissible P m' (tau P m') →
      m ≤ m' → tau P m ≤ tau P m') := by
  refine ⟨cm_equil P hS m, fun q hq => cm_eq_tau P hS m q hq,
    fun c hc hne => cm_luc_tau P hS m c hc hne, fun m' _ hmm => ?_⟩
  unfold tau
  exact min_le_min le_rfl (max_le_max hmm le_rfl)
