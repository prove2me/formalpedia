-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_ae_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:39:32.319505+00:00
-- url     : https://prove2.me/submissions/82c61e75-018c-431b-8cc7-7bb33ea2e2a8

import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
namespace AvramChat06M

def arrivalForPoissonAE {Ω : Type*} (τ : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), τ i ω

noncomputable def countForPoissonAE {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < arrivalForPoissonAE τ n ω}

end AvramChat06M

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun k =>
      AvramChat06M.arrivalForPoissonAE τ k ω) atTop atTop)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun k =>
      AvramChat06M.arrivalForPoissonAE τ k ω)) :
    {ω | AvramChat06M.countForPoissonAE τ t ω = n + 1} =ᵐ[P]
      ({ω | t < AvramChat06M.arrivalForPoissonAE τ (n + 1) ω} \
       {ω | t < AvramChat06M.arrivalForPoissonAE τ n ω}) := by
  filter_upwards [hmono] with ω hm
  apply propext
  change sInf {k : ℕ | t < AvramChat06M.arrivalForPoissonAE τ k ω} = n + 1 ↔
    (t < AvramChat06M.arrivalForPoissonAE τ (n + 1) ω ∧ ¬ t < AvramChat06M.arrivalForPoissonAE τ n ω)
  constructor
  · intro h
    have hne : {k : ℕ | t < AvramChat06M.arrivalForPoissonAE τ k ω}.Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty] at hc
      rw [hc, Nat.sInf_empty] at h
      omega
    have h1 := Nat.sInf_mem hne
    rw [h] at h1
    exact ⟨h1, Nat.notMem_of_lt_sInf (s := {k : ℕ | t < AvramChat06M.arrivalForPoissonAE τ k ω}) (by omega)⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.sInf_le h1)
    by_contra hlt
    push Not at hlt
    have hne : {k : ℕ | t < AvramChat06M.arrivalForPoissonAE τ k ω}.Nonempty := ⟨_, h1⟩
    have hmem := Nat.sInf_mem hne
    simp only [mem_setOf_eq] at hmem
    exact h2 (lt_of_lt_of_le hmem (hm (by omega)))
