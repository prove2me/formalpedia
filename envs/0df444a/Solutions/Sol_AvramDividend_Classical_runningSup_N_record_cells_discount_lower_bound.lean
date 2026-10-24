-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_N_record_cells_discount_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:16:52.932782+00:00
-- url     : https://prove2.me/submissions/9ce396f1-d0e7-497c-9eb5-4374c646d08a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (N : ℕ) (u : ℕ → ℝ≥0)
    (hu : ∀ k : ℕ, k ≤ N → ((u k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))))
    (hord : ∀ k : ℕ, k < N → ((u k : ℝ) ≤ (u (k + 1) : ℝ)))
    (hSurvive : ENNReal.ofReal ((u N : ℝ)) < τ) :
    ∑ k ∈ Finset.range N,
        (ENNReal.ofReal (Real.exp (-(q * ((u (k + 1) : ℝ)))))) * ENNReal.ofReal h ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc ((u 0 : ℝ)) ((u N : ℝ))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let ν : Measure ℝ := μ.restrict (paymentTimes τ)
  let W : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  let R : ℝ → ℝ → ℝ≥0∞ := fun a c =>
    ∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc a c then W r else 0 ∂μ
  have hRepr (a c : ℝ) :
      R a c = ∫⁻ r in Set.Ioc a c, W r ∂ν := by
    change (∫⁻ r, if r ∈ Set.Ioc a c then W r else 0 ∂ν) =
      ∫⁻ r in Set.Ioc a c, W r ∂ν
    have hfun :
        (fun r : ℝ => if r ∈ Set.Ioc a c then W r else 0) =
        (Set.Ioc a c).indicator W := by
      funext r
      by_cases hr : r ∈ Set.Ioc a c
      · simp [hr, Set.indicator_of_mem hr]
      · simp [hr, Set.indicator_of_notMem hr]
    rw [hfun]
    exact lintegral_indicator measurableSet_Ioc W
  -- Prefix ordering: u i ≤ u j for i ≤ j ≤ n (needs only successive hord).
  have hle : ∀ (n : ℕ) (v : ℕ → ℝ≥0),
      (∀ k : ℕ, k < n → ((v k : ℝ) ≤ (v (k + 1) : ℝ))) →
      ∀ (i j : ℕ), i ≤ j → j ≤ n → ((v i : ℝ) ≤ (v j : ℝ)) := by
    intro n v ho i j hij hjN
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ m hmn ih =>
      exact le_trans (ih (by omega)) (ho m hjN)
  -- Key induction on the number of cells, generalizing the record selection.
  have key : ∀ (n : ℕ) (v : ℕ → ℝ≥0),
      (∀ k : ℕ, k ≤ n → ((v k : ℝ≥0∞) =
        (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)))) →
      (∀ k : ℕ, k < n → ((v k : ℝ) ≤ (v (k + 1) : ℝ))) →
      ENNReal.ofReal ((v n : ℝ)) < τ →
      ∑ k ∈ Finset.range n,
          (ENNReal.ofReal (Real.exp (-(q * ((v (k + 1) : ℝ)))))) * ENNReal.ofReal h ≤
        R ((v 0 : ℝ)) ((v n : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro v hv ho hs
      simp only [Finset.sum_range_zero]
      exact zero_le
    | succ n ih =>
      intro v hv ho hs
      have hvN : ∀ k : ℕ, k ≤ n → ((v k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))) :=
        fun k hk => hv k (Nat.le_step hk)
      have hoN : ∀ k : ℕ, k < n → ((v k : ℝ) ≤ (v (k + 1) : ℝ)) :=
        fun k hk => ho k (by omega)
      have hsN : ENNReal.ofReal ((v n : ℝ)) < τ :=
        lt_of_le_of_lt
          (ENNReal.ofReal_le_ofReal (hle (n + 1) v
            (fun k hk => ho k hk) n (n + 1) (Nat.le_succ n) (le_refl (n + 1))))
          hs
      have hIH := ih v hvN hoN hsN
      -- Last cell (levels b + n*h → b + (n+1)*h) via the ACCEPTED one-cell lemma.
      have hlevel : b + ((n + 1 : ℕ) : ℝ) * h = (b + (n : ℝ) * h) + h := by
        push_cast
        ring
      have hbn : 0 ≤ b + (n : ℝ) * h :=
        add_nonneg hb (mul_nonneg (Nat.cast_nonneg n) hh)
      have huvN : ((v n : ℝ≥0∞) =
          (⨅ (r : ℝ≥0) (_ : (b + (n : ℝ) * h) < X.X r ω), (r : ℝ≥0∞))) :=
        hv n (Nat.le_succ n)
      have huvS : ((v (n + 1) : ℝ≥0∞) =
          (⨅ (r : ℝ≥0) (_ : (b + (n : ℝ) * h) + h < X.X r ω), (r : ℝ≥0∞))) := by
        rw [← hlevel]
        exact hv (n + 1) (le_refl (n + 1))
      have hcn : ENNReal.ofReal (Real.exp (-(q * ((v (n + 1) : ℝ))))) * ENNReal.ofReal h ≤
          R ((v n : ℝ)) ((v (n + 1) : ℝ)) :=
        (runningSup_stopped_firstRecord_step_discount_bounds
          X ω τ q hq _ _ hbn hh _ _ huvN huvS hs).1
      -- Adjacent additivity of the stopped reward.
      have h0n : ((v 0 : ℝ)) ≤ ((v n : ℝ)) :=
        hle (n + 1) v (fun k hk => ho k hk) 0 n (Nat.zero_le n)
          (by omega)
      have hnn1 : ((v n : ℝ)) ≤ ((v (n + 1) : ℝ)) := ho n (Nat.lt_succ_self n)
      have hAdd : R ((v 0 : ℝ)) ((v (n + 1) : ℝ)) =
          R ((v 0 : ℝ)) ((v n : ℝ)) + R ((v n : ℝ)) ((v (n + 1) : ℝ)) := by
        rw [hRepr, hRepr, hRepr]
        exact lintegral_Ioc_adjacent_add ν W _ _ _ h0n hnn1
      rw [Finset.sum_range_succ, hAdd]
      exact add_le_add hIH hcn
  have hfin := key N u hu hord hSurvive
  exact hfin
