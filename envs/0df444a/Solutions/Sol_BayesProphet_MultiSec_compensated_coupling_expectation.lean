-- Prove2me | solution 1 for BayesProphet.MultiSec.compensated_coupling_expectation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:59:00.712502+00:00
-- url     : https://prove2.me/submissions/c0019e31-cfcc-494c-8f5a-6aaba1d29d77

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Theorems.Thm_BayesProphet_MultiSec_compensated_coupling_identity

namespace BayesProphet.MultiSec.CCEAux
open BayesProphet.MultiSec OnlineProblem

section General
variable {S Θ A : Type*} (P : OnlineProblem S Θ A)

lemma offVal_le (θ : ℕ → Θ) (c₂ : ℝ)
    (hP : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂) :
    ∀ t s, P.offVal θ t s ≤ t * c₂
  | 0, _ => by simp [OnlineProblem.offVal]
  | t + 1, s => by
    obtain ⟨a0, ha0, hmax, hc⟩ := hP s (θ (t + 1))
    haveI : Nonempty (P.feasible s) := ⟨⟨a0, ha0⟩⟩
    simp only [OnlineProblem.offVal]
    apply ciSup_le
    rintro ⟨a, ha⟩
    have h1 := hmax a ha
    have h2 := offVal_le θ c₂ hP t (P.trans a s (θ (t + 1)))
    push_cast
    linarith

lemma le_offVal (θ : ℕ → Θ) (c₂ : ℝ)
    (hP : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂)
    (t : ℕ) (s : S) (a : A) (ha : a ∈ P.feasible s) :
    P.reward a s (θ (t + 1)) + P.offVal θ t (P.trans a s (θ (t + 1))) ≤ P.offVal θ (t + 1) s := by
  obtain ⟨a0, ha0, hmax, hc⟩ := hP s (θ (t + 1))
  simp only [OnlineProblem.offVal]
  have hbdd : BddAbove (Set.range fun a : P.feasible s =>
      P.reward a s (θ (t + 1)) + P.offVal θ t (P.trans a s (θ (t + 1)))) := by
    refine ⟨c₂ + t * c₂, ?_⟩
    rintro _ ⟨⟨a', ha'⟩, rfl⟩
    have h1 := hmax a' ha'
    have h2 := offVal_le P θ c₂ hP t (P.trans a' s (θ (t + 1)))
    simp only
    linarith
  exact le_ciSup hbdd (⟨a, ha⟩ : P.feasible s)

end General

end BayesProphet.MultiSec.CCEAux

open BayesProphet.MultiSec BayesProphet.MultiSec.CCEAux OnlineProblem MeasureTheory in
theorem solution {S Θ A : Type*} (P : OnlineProblem S Θ A)
    (hP : P.StandingAssumption) (T : ℕ) (π : Policy S Θ A) (hπ : P.IsOnlinePolicy T π)
    (s₀ : S) {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℕ → Θ)
    (hint : MeasureTheory.Integrable (fun ω => P.regret π T s₀ (X ω)) μ)
    (C : ℝ)
    (hC : ∀ t ∈ Finset.Icc 1 T, ∀ (s : S), ∀ a ∈ P.feasible s, ∀ ω : Ω,
      P.margComp (X ω) t a s ≤ C) :
    ∫ ω, P.regret π T s₀ (X ω) ∂μ ≤
      C * ∑ t ∈ Finset.Icc 1 T,
        (μ {ω | P.Disagree (X ω) t (π t (X ω) (P.onlineState π T s₀ (X ω) t))
          (P.onlineState π T s₀ (X ω) t)}).toReal := by
  classical
  obtain ⟨c₁, c₂, hc1, hc2, hc⟩ := hP
  have hP' : ∀ (s : S) (j : Θ), ∃ a ∈ P.feasible s,
      (∀ a' ∈ P.feasible s, P.reward a' s j ≤ P.reward a s j) ∧ P.reward a s j ≤ c₂ := by
    intro s j
    obtain ⟨a, ha, h1, -, h3⟩ := hc s j
    exact ⟨a, ha, h1, h3⟩
  have hPsa : P.StandingAssumption := ⟨c₁, c₂, hc1, hc2, hc⟩
  set D : ℕ → Set Ω := fun t => {ω | P.Disagree (X ω) t (π t (X ω) (P.onlineState π T s₀ (X ω) t))
          (P.onlineState π T s₀ (X ω) t)} with hD
  set M : ℕ → Set Ω := fun t => toMeasurable μ (D t) with hM
  -- the compensation bound is nonnegative as soon as T ≥ 1
  have hC0 : 1 ≤ T → 0 ≤ C := by
    intro hT
    obtain ⟨ω0⟩ : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := measure_univ (μ := μ)
      rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
      exact zero_ne_one this
    obtain ⟨a, ha, -⟩ := hP' s₀ (X ω0 1)
    have h1 := hC 1 (by simp; omega) s₀ a ha ω0
    have h2 := le_offVal P (X ω0) c₂ hP' 0 s₀ a ha
    unfold OnlineProblem.margComp at h1
    simp only [Nat.sub_self, zero_add] at h1 h2
    linarith
  set g : Ω → ℝ := fun ω => ∑ t ∈ Finset.Icc 1 T, C * (M t).indicator (fun _ => (1 : ℝ)) ω
    with hg
  have hgint : Integrable g μ := by
    apply integrable_finset_sum
    intro t _
    exact ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable μ (D t))).const_mul C
  have hle : ∀ ω, P.regret π T s₀ (X ω) ≤ g ω := by
    intro ω
    rw [compensated_coupling_identity P hPsa T π hπ s₀ (X ω)]
    apply Finset.sum_le_sum
    intro t ht
    have hT : 1 ≤ T := le_trans (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
    unfold OnlineProblem.disagreeInd
    split_ifs with hd
    · have hmem : ω ∈ M t := subset_toMeasurable μ (D t) hd
      rw [Set.indicator_of_mem hmem, mul_one, mul_one]
      exact hC t ht _ _ (hπ.1 t ht _ _) ω
    · rw [mul_zero]
      have : 0 ≤ (M t).indicator (fun _ => (1 : ℝ)) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      exact mul_nonneg (hC0 hT) this
  refine le_trans (integral_mono hint hgint hle) (le_of_eq ?_)
  rw [hg, integral_finset_sum _ (fun t _ =>
    ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable μ (D t))).const_mul C)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [integral_const_mul]
  congr 1
  rw [integral_indicator_const _ (measurableSet_toMeasurable μ (D t)), smul_eq_mul, mul_one]
  rw [measureReal_def, measure_toMeasurable]
