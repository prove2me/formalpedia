-- Prove2me | solution 1 for FoundationsML.Boosting.adaboost_margin_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:56:41.251564+00:00
-- url     : https://prove2.me/submissions/675b1002-451f-48b8-84df-36fe63d2ab9e

import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizedEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

lemma aux_amb_dist_succ {X : Type*} {m : ℕ} (S : Fin m → X) (y : Fin m → ℝ)
    (h : ℕ → X → ℝ) (t : ℕ) (i : Fin m) :
    AdaBoostDist S y h (t + 1) i =
      AdaBoostDist S y h t i *
        Real.exp (-AdaBoostAlpha (AdaBoostEpsilon S y h t) * y i * h t (S i)) /
        AdaBoostNormalizer (AdaBoostEpsilon S y h t) := rfl

lemma aux_amb_ens_succ {X : Type*} {m : ℕ} (S : Fin m → X) (y : Fin m → ℝ)
    (h : ℕ → X → ℝ) (t : ℕ) (x : X) :
    AdaBoostEnsemble S y h (t + 1) x =
      AdaBoostEnsemble S y h t x + AdaBoostAlpha (AdaBoostEpsilon S y h t) * h t x := by
  simp only [AdaBoostEnsemble, Finset.sum_range_succ]

lemma aux_amb_dist_closed {X : Type*} {m : ℕ} (S : Fin m → X) (y : Fin m → ℝ)
    (h : ℕ → X → ℝ) (t : ℕ) (i : Fin m) :
    AdaBoostDist S y h t i =
      Real.exp (-(y i * AdaBoostEnsemble S y h t (S i))) /
        ((m : ℝ) * ∏ s ∈ Finset.range t, AdaBoostNormalizer (AdaBoostEpsilon S y h s)) := by
  induction t with
  | zero => simp [AdaBoostDist, AdaBoostEnsemble]
  | succ t ih =>
    rw [aux_amb_dist_succ, ih, Finset.prod_range_succ, aux_amb_ens_succ,
      div_mul_eq_mul_div, div_div, ← Real.exp_add]
    congr 1
    · congr 1
      ring
    · ring

lemma aux_amb_eps_facts (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    0 < AdaBoostAlpha ε ∧ 0 < AdaBoostNormalizer ε ∧
      (1 - ε) * Real.exp (-AdaBoostAlpha ε) + ε * Real.exp (AdaBoostAlpha ε) =
        AdaBoostNormalizer ε ∧
      ∀ ρ : ℝ, Real.exp (ρ * AdaBoostAlpha ε) * AdaBoostNormalizer ε =
        2 * Real.sqrt (ε ^ (1 - ρ) * (1 - ε) ^ (1 + ρ)) := by
  have h1' : 0 < 1 - ε := by linarith
  set L1 := Real.log ε with hL1
  set L2 := Real.log (1 - ε) with hL2
  have e1 : Real.exp L1 = ε := Real.exp_log h0
  have e2 : Real.exp L2 = 1 - ε := Real.exp_log h1'
  have hα : AdaBoostAlpha ε = 1 / 2 * (L2 - L1) := by
    unfold AdaBoostAlpha
    rw [Real.log_div h1'.ne' h0.ne']
  have hZ : AdaBoostNormalizer ε = 2 * Real.exp ((L1 + L2) / 2) := by
    unfold AdaBoostNormalizer
    have : Real.exp ((L1 + L2) / 2) * Real.exp ((L1 + L2) / 2) = ε * (1 - ε) := by
      rw [← Real.exp_add, show (L1 + L2) / 2 + (L1 + L2) / 2 = L1 + L2 by ring,
        Real.exp_add, e1, e2]
    rw [← this, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hlt : L1 < L2 := Real.log_lt_log h0 (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hα]; nlinarith
  · rw [hZ]; positivity
  · rw [hα, hZ]
    conv_lhs => rw [← e2, ← e1]
    rw [← Real.exp_add, ← Real.exp_add,
      show L2 + -(1 / 2 * (L2 - L1)) = (L1 + L2) / 2 by ring,
      show L1 + 1 / 2 * (L2 - L1) = (L1 + L2) / 2 by ring]
    ring
  · intro ρ
    rw [hα, hZ, Real.rpow_def_of_pos h0, Real.rpow_def_of_pos h1', ← hL1, ← hL2]
    have : Real.exp (L1 * (1 - ρ)) * Real.exp (L2 * (1 + ρ)) =
        Real.exp ((L1 * (1 - ρ) + L2 * (1 + ρ)) / 2) *
          Real.exp ((L1 * (1 - ρ) + L2 * (1 + ρ)) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [this, Real.sqrt_mul_self (Real.exp_pos _).le]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring

lemma aux_amb_sum_one {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1 / 2) :
    ∀ t ≤ T, ∑ i, AdaBoostDist S y h t i = 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [AdaBoostDist]
    field_simp
  | succ t ih =>
    intro ht
    have htT : t < T := by omega
    have hsum := ih (by omega)
    obtain ⟨h0, h1⟩ := hweak t htT
    obtain ⟨_, hZpos, hnorm, _⟩ := aux_amb_eps_facts _ h0 h1
    set ε := AdaBoostEpsilon S y h t with hε
    set α := AdaBoostAlpha ε with hα
    have key : ∀ i, Real.exp (-α * y i * h t (S i)) =
        Real.exp (-α) + (if h t (S i) = y i then 0 else 1) *
          (Real.exp α - Real.exp (-α)) := by
      intro i
      rcases hy i with hyi | hyi <;> rcases hh t htT (S i) with hhi | hhi <;>
        simp [hyi, hhi] <;> norm_num
    simp only [aux_amb_dist_succ]
    rw [← Finset.sum_div, div_eq_one_iff_eq hZpos.ne', ← hε, ← hα]
    simp_rw [key, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
    have hW : ∑ i, AdaBoostDist S y h t i *
        ((if h t (S i) = y i then 0 else 1) * (Real.exp α - Real.exp (-α))) =
        ε * (Real.exp α - Real.exp (-α)) := by
      rw [hε, AdaBoostEpsilon, WeightedError, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hW, ← hnorm]
    ring

lemma aux_amb_phi (ρ A u : ℝ) (hρ : 0 < ρ) (hA : 0 ≤ A) :
    PhiRho ρ u ≤ Real.exp (ρ * A - A * u) := by
  unfold PhiRho
  by_cases hu : u ≤ ρ
  · have : 0 ≤ ρ * A - A * u := by nlinarith
    exact (min_le_left _ _).trans (Real.one_le_exp this)
  · push Not at hu
    have : 1 - u / ρ < 0 := by
      have : 1 < u / ρ := (one_lt_div hρ).mpr hu
      linarith
    rw [max_eq_left this.le]
    exact (min_le_right _ _).trans (Real.exp_pos _).le

end FoundationsML.Boosting

open FoundationsML.Boosting

theorem solution {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1 / 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    EmpiricalMarginLoss ρ S y (AdaBoostNormalizedEnsemble S y h T) ≤
      2 ^ T * ∏ t ∈ Finset.range T,
        Real.sqrt ((AdaBoostEpsilon S y h t) ^ (1 - ρ) *
          (1 - AdaBoostEpsilon S y h t) ^ (1 + ρ)) := by
  set A := ∑ t ∈ Finset.range T, AdaBoostAlpha (AdaBoostEpsilon S y h t) with hAdef
  set P := ∏ s ∈ Finset.range T, AdaBoostNormalizer (AdaBoostEpsilon S y h s) with hPdef
  have hαpos : ∀ t ∈ Finset.range T, 0 < AdaBoostAlpha (AdaBoostEpsilon S y h t) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    exact (aux_amb_eps_facts _ (hweak t ht').1 (hweak t ht').2).1
  have hZpos : ∀ t ∈ Finset.range T, 0 < AdaBoostNormalizer (AdaBoostEpsilon S y h t) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    exact (aux_amb_eps_facts _ (hweak t ht').1 (hweak t ht').2).2.1
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun t ht => (hαpos t ht).le
  have hP0 : 0 < P := Finset.prod_pos hZpos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the margin rescaling identity
  have hscale : ∀ i, A * (y i * AdaBoostNormalizedEnsemble S y h T (S i)) =
      y i * AdaBoostEnsemble S y h T (S i) := by
    intro i
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp [AdaBoostNormalizedEnsemble, AdaBoostEnsemble, hAdef]
    · have hApos : 0 < A :=
        Finset.sum_pos hαpos (Finset.nonempty_range_iff.mpr hT.ne')
      unfold AdaBoostNormalizedEnsemble
      rw [← hAdef]
      field_simp
  -- exp of the negative margin in terms of the final distribution
  have hexp : ∀ i, Real.exp (-(y i * AdaBoostEnsemble S y h T (S i))) =
      AdaBoostDist S y h T i * ((m : ℝ) * P) := by
    intro i
    rw [aux_amb_dist_closed S y h T i, ← hPdef, div_mul_cancel₀]
    positivity
  have hsum1 := aux_amb_sum_one hm S y hy T h hh hweak T le_rfl
  -- the per-round identity
  have hround : Real.exp (ρ * A) * P = 2 ^ T * ∏ t ∈ Finset.range T,
        Real.sqrt ((AdaBoostEpsilon S y h t) ^ (1 - ρ) *
          (1 - AdaBoostEpsilon S y h t) ^ (1 + ρ)) := by
    rw [hAdef, hPdef, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    rw [show (2 : ℝ) ^ T = ∏ t ∈ Finset.range T, (2 : ℝ) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    exact (aux_amb_eps_facts _ (hweak t ht').1 (hweak t ht').2).2.2.2 ρ
  rw [← hround]
  unfold EmpiricalMarginLoss
  calc (1 / (m : ℝ)) * ∑ i, PhiRho ρ (y i * AdaBoostNormalizedEnsemble S y h T (S i))
      ≤ (1 / (m : ℝ)) * ∑ i, Real.exp (ρ * A - y i * AdaBoostEnsemble S y h T (S i)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← hscale i]
        exact aux_amb_phi ρ A _ hρ hA0
    _ = (1 / (m : ℝ)) * ∑ i, Real.exp (ρ * A) * (AdaBoostDist S y h T i * ((m : ℝ) * P)) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hexp i, ← Real.exp_add]
        ring_nf
    _ = Real.exp (ρ * A) * P := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, hsum1]
        field_simp
