-- Prove2me | solution 1 for FoundationsML.Boosting.adaboost_empirical_error_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:08:06.49851+00:00
-- url     : https://prove2.me/submissions/59e2ee1c-9d88-4095-b3c3-4bfc1ede72be

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalError
import Definitions.Def_FoundationsML_Boosting_AdaBoostEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace AB88
open FoundationsML.Boosting

theorem dist_formula {X : Type*} {m : ℕ} (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ)
    (t : ℕ) (i : Fin m) :
    AdaBoostDist S y h t i = Real.exp (-(y i * AdaBoostEnsemble S y h t (S i))) /
      ((m : ℝ) * ∏ s ∈ Finset.range t, AdaBoostNormalizer (AdaBoostEpsilon S y h s)) := by
  induction t with
  | zero => simp [AdaBoostDist, AdaBoostEnsemble]
  | succ t ih =>
    show AdaBoostDist S y h t i * Real.exp (-AdaBoostAlpha (AdaBoostEpsilon S y h t) * y i * h t (S i))
      / AdaBoostNormalizer (AdaBoostEpsilon S y h t) = _
    rw [ih, Finset.prod_range_succ, div_mul_eq_mul_div, div_div, ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [AdaBoostEnsemble, Finset.sum_range_succ]
    ring

theorem normalizer_eq (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    (1 - ε) * Real.exp (-AdaBoostAlpha ε) + ε * Real.exp (AdaBoostAlpha ε) = AdaBoostNormalizer ε := by
  have hu : 0 < (1 - ε) / ε := div_pos (by linarith) h0
  have hsq : Real.exp (AdaBoostAlpha ε) ^ 2 = (1 - ε) / ε := by
    rw [← Real.exp_nat_mul, AdaBoostAlpha]; push_cast
    rw [show (2:ℝ) * (1 / 2 * Real.log ((1 - ε) / ε)) = Real.log ((1 - ε) / ε) by ring,
      Real.exp_log hu]
  rw [Real.exp_neg]
  have hapos := Real.exp_pos (AdaBoostAlpha ε)
  set a := Real.exp (AdaBoostAlpha ε) with ha
  have hp : 0 ≤ ε * (1 - ε) := by nlinarith
  have e1 : ε * a = Real.sqrt (ε * (1 - ε)) := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hp (by positivity)]
    have : a * a = (1 - ε) / ε := by rw [← hsq]; ring
    field_simp at this ⊢; nlinarith [this]
  have e2 : (1 - ε) * a⁻¹ = Real.sqrt (ε * (1 - ε)) := by
    rw [← e1]; field_simp
    have : a ^ 2 * ε = 1 - ε := by rw [hsq]; field_simp
    linarith
  rw [e1, e2, AdaBoostNormalizer]; ring

theorem normalizer_le (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    AdaBoostNormalizer ε ≤ Real.exp (-2 * (1 / 2 - ε) ^ 2) := by
  have hp : 0 ≤ ε * (1 - ε) := by nlinarith
  have hE := Real.add_one_le_exp (-4 * (1 / 2 - ε) ^ 2)
  have hsq : Real.exp (-2 * (1 / 2 - ε) ^ 2) ^ 2 = Real.exp (-4 * (1 / 2 - ε) ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [AdaBoostNormalizer]
  have hs := Real.sq_sqrt hp
  have hs0 := Real.sqrt_nonneg (ε * (1 - ε))
  have hpos := Real.exp_pos (-2 * (1 / 2 - ε) ^ 2)
  nlinarith [sq_nonneg (2 * Real.sqrt (ε * (1 - ε)) - Real.exp (-2 * (1 / 2 - ε) ^ 2)),
    sq_nonneg (2 * Real.sqrt (ε * (1 - ε)) + Real.exp (-2 * (1 / 2 - ε) ^ 2))]


theorem eps_bounds {X : Type*} {m : ℕ} (D : Fin m → ℝ) (S : Fin m → X) (y : Fin m → ℝ) (g : X → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hs : ∑ i, D i = 1) :
    0 ≤ WeightedError D S y g ∧ WeightedError D S y g ≤ 1 := by
  unfold WeightedError
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hD i) (by split_ifs <;> norm_num)
  · rw [← hs]; exact Finset.sum_le_sum fun i _ => by
      have := hD i; split_ifs <;> nlinarith

theorem step {X : Type*} {m : ℕ} (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (h : ℕ → X → ℝ) (t : ℕ) (hh : ∀ x, h t x = 1 ∨ h t x = -1)
    (hD : ∀ i, 0 ≤ AdaBoostDist S y h t i) (hs : ∑ i, AdaBoostDist S y h t i = 1)
    (h0 : AdaBoostEpsilon S y h t ≠ 0) (h1 : AdaBoostEpsilon S y h t ≠ 1) :
    (∀ i, 0 ≤ AdaBoostDist S y h (t + 1) i) ∧ ∑ i, AdaBoostDist S y h (t + 1) i = 1 := by
  obtain ⟨e0, e1⟩ := eps_bounds (AdaBoostDist S y h t) S y (h t) hD hs
  have e0' : 0 < AdaBoostEpsilon S y h t := lt_of_le_of_ne e0 (Ne.symm h0)
  have e1' : AdaBoostEpsilon S y h t < 1 := lt_of_le_of_ne e1 h1
  have hZ := normalizer_eq _ e0' e1'
  set ε := AdaBoostEpsilon S y h t with hε
  set α := AdaBoostAlpha ε
  have hZpos : 0 < AdaBoostNormalizer ε := by
    rw [← hZ]; have := Real.exp_pos α; have := Real.exp_pos (-α); positivity
  have hdef : ∀ i, AdaBoostDist S y h (t + 1) i =
      AdaBoostDist S y h t i * Real.exp (-α * y i * h t (S i)) / AdaBoostNormalizer ε := fun i => rfl
  have key : ∀ i, AdaBoostDist S y h t i * Real.exp (-α * y i * h t (S i)) =
      AdaBoostDist S y h t i * Real.exp (-α) + (Real.exp α - Real.exp (-α)) *
        (AdaBoostDist S y h t i * (if h t (S i) = y i then 0 else 1)) := by
    intro i
    rcases hy i with h' | h' <;> rcases hh (S i) with h'' | h'' <;> rw [h', h''] <;> norm_num <;> ring_nf
  refine ⟨fun i => ?_, ?_⟩
  · rw [hdef]; have := hD i; positivity
  · simp_rw [hdef, ← Finset.sum_div, key, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, hs]
    rw [div_eq_one_iff_eq hZpos.ne', ← hZ]
    have : ∑ i, AdaBoostDist S y h t i * (if h t (S i) = y i then 0 else 1) = ε := rfl
    rw [this]; ring

theorem invariant {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1) :
    ∀ t ≤ T, (∀ i, 0 ≤ AdaBoostDist S y h t i) ∧ ∑ i, AdaBoostDist S y h t i = 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i => by simp [AdaBoostDist], ?_⟩
    simp [AdaBoostDist]; field_simp
  | succ t ih =>
    intro ht
    obtain ⟨a, b⟩ := ih (by omega)
    exact step S y hy h t (hh t (by omega)) a b (hne t (by omega)).1 (hne t (by omega)).2

theorem main {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1) :
    EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) := by
  have inv := invariant hm S y hy T h hh hne
  have hb : ∀ t < T, 0 ≤ AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t ≤ 1 := fun t ht =>
    eps_bounds _ S y (h t) (inv t ht.le).1 (inv t ht.le).2
  set P := ∏ s ∈ Finset.range T, AdaBoostNormalizer (AdaBoostEpsilon S y h s) with hP
  have hPpos : 0 < P := by
    apply Finset.prod_pos; intro t ht
    have ht := Finset.mem_range.mp ht
    have e0 : 0 < AdaBoostEpsilon S y h t := lt_of_le_of_ne (hb t ht).1 (Ne.symm (hne t ht).1)
    have e1 : AdaBoostEpsilon S y h t < 1 := lt_of_le_of_ne (hb t ht).2 (hne t ht).2
    unfold AdaBoostNormalizer
    have : 0 < AdaBoostEpsilon S y h t * (1 - AdaBoostEpsilon S y h t) := by nlinarith
    positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : ∀ i, Real.exp (-(y i * AdaBoostEnsemble S y h T (S i))) =
      (m * P) * AdaBoostDist S y h T i := by
    intro i; rw [dist_formula, ← hP]; field_simp
  have h1 : EmpiricalError S y (AdaBoostEnsemble S y h T) ≤ P := by
    unfold EmpiricalError
    calc (1 / (m : ℝ)) * ∑ i, (if y i * AdaBoostEnsemble S y h T (S i) ≤ 0 then (1 : ℝ) else 0)
        ≤ (1 / (m : ℝ)) * ∑ i, Real.exp (-(y i * AdaBoostEnsemble S y h T (S i))) := by
          gcongr with i
          split_ifs with hc
          · exact Real.one_le_exp (by linarith)
          · exact (Real.exp_pos _).le
      _ = P := by
          simp_rw [hexp, ← Finset.mul_sum, (inv T le_rfl).2]; field_simp
  refine h1.trans ?_
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro t ht
    have ht := Finset.mem_range.mp ht
    unfold AdaBoostNormalizer; positivity
  · intro t ht
    have ht := Finset.mem_range.mp ht
    exact normalizer_le _ (hb t ht).1 (hb t ht).2

end AB88

open FoundationsML.Boosting in
theorem solution {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hne : ∀ t < T, AdaBoostEpsilon S y h t ≠ 0 ∧ AdaBoostEpsilon S y h t ≠ 1) :
    EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
        Real.exp (-2 * ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) ∧
      (∀ γ : ℝ, 0 ≤ γ → (∀ t < T, γ ≤ 1 / 2 - AdaBoostEpsilon S y h t) →
        EmpiricalError S y (AdaBoostEnsemble S y h T) ≤
          Real.exp (-2 * γ ^ 2 * T)) := by
  have H := AB88.main hm S y hy T h hh hne
  refine ⟨H, fun γ hγ hle => H.trans ?_⟩
  apply Real.exp_le_exp.mpr
  have : (T : ℝ) * γ ^ 2 ≤ ∑ t ∈ Finset.range T, (1 / 2 - AdaBoostEpsilon S y h t) ^ 2 := by
    have := Finset.sum_le_sum (s := Finset.range T) (f := fun _ => γ ^ 2)
      (g := fun t => (1 / 2 - AdaBoostEpsilon S y h t) ^ 2) (fun t ht => by
        have := hle t (Finset.mem_range.mp ht)
        exact pow_le_pow_left₀ hγ this 2)
    simpa using this
  nlinarith
