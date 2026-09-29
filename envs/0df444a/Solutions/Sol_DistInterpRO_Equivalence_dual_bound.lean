-- Prove2me | solution 1 for DistInterpRO.Equivalence.dual_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:01:06.129797+00:00
-- url     : https://prove2.me/submissions/485412ef-0f18-41f5-ac73-b39b810b43b8

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory


namespace DistInterpRO.Equivalence

theorem carried_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ))
    (hZm : ∀ i, MeasurableSet (Z i))
    (μ : Measure (Fin m → ℝ)) (hμ : μ ∈ distSet c Z) :
    μ (⋃ i, Z i)ᶜ = 0 ∧ expect μ f = expect (μ.restrict (⋃ i, Z i)) f := by
  obtain ⟨hP, hS⟩ := hμ
  have h1 := hS Finset.univ
  simp only [Finset.mem_univ, Set.iUnion_true, hsum, ENNReal.ofReal_one] at h1
  have hm : MeasurableSet (⋃ i, Z i) := MeasurableSet.iUnion hZm
  have hc : μ (⋃ i, Z i)ᶜ = 0 := by
    rw [measure_compl hm (measure_ne_top _ _), measure_univ]
    have : μ (⋃ i, Z i) = 1 := le_antisymm prob_le_one h1
    rw [this]; simp
  refine ⟨hc, ?_⟩
  have : μ.restrict (⋃ i, Z i) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have : {a | ¬ a ∈ ⋃ i, Z i} = (⋃ i, Z i)ᶜ := rfl
    rw [this]; exact hc
  rw [this]

theorem dual_core {m n : ℕ} (f : (Fin m → ℝ) → ℝ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (α : Finset (Fin n) → ℝ) (hα : IsDualFeasible Z f α) :
    ∑ i, c i * ∑ S : Finset (Fin n), α S * (if i ∈ S then (1 : ℝ) else 0) ≤
      ∑ i, c i * ⨅ x : Z i, f x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hc i).le
  haveI : Nonempty (Z i) := (hZne i).to_subtype
  apply le_ciInf
  rintro ⟨x, hx⟩
  have hxU : x ∈ ⋃ i, Z i := Set.mem_iUnion.2 ⟨i, hx⟩
  refine le_trans ?_ (hα.1 x hxU)
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = Finset.univ
  · subst hS
    simp only [Finset.mem_univ, if_true, Set.iUnion_true, hxU]
    exact le_rfl
  · have h0 := hα.2 S hS
    apply mul_le_mul_of_nonneg_left _ h0
    by_cases hi : i ∈ S
    · have : x ∈ ⋃ j ∈ S, Z j := Set.mem_biUnion hi hx
      simp [hi, this]
    · simp only [hi, if_false]
      split_ifs <;> norm_num

end DistInterpRO.Equivalence

open DistInterpRO.Equivalence


theorem solution {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (α : Finset (Fin n) → ℝ) (hα : IsDualFeasible Z f α) :
    ∑ i, c i * ∑ S : Finset (Fin n), α S * (if i ∈ S then (1 : ℝ) else 0) ≤
      ∑ i, c i * ⨅ x : Z i, f x := by
  exact dual_core f c hc Z hZne α hα
