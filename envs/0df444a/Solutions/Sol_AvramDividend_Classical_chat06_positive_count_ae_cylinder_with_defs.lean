-- Prove2me | solution 1 for AvramDividend.Classical.chat06_positive_count_ae_cylinder_with_defs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:16:53.550749+00:00
-- url     : https://prove2.me/submissions/19ed74f1-fb63-47db-bb13-c85e1d579e99

import Definitions.Def_AvramChat06_RenewalArrivalCountAE
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Poisson.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramChat06

/-- Arrival count cylinder equality holds almost surely when
nonexplosion and nondecreasing arrivals hold almost surely,
without imposing impossible every-path constraints on an
exponential product sample space. -/
theorem positive_count_cylinder_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun k =>
      arrivalForPoissonAE τ k ω) atTop atTop)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun k =>
      arrivalForPoissonAE τ k ω)) :
    {ω | countForPoissonAE τ t ω = n + 1} =ᵐ[P]
      ({ω | t < arrivalForPoissonAE τ (n + 1) ω} \
       {ω | t < arrivalForPoissonAE τ n ω}) := by
  filter_upwards [hdiv, hmono] with ω hd hm
  let A : Set Ω := {z | t < arrivalForPoissonAE τ n z}
  let B : Set Ω := {z | t < arrivalForPoissonAE τ (n + 1) z}
  have hnonempty : {k : ℕ | t < arrivalForPoissonAE τ k ω}.Nonempty :=
    (hd.eventually_gt_atTop t).exists
  have hiff : countForPoissonAE τ t ω = n + 1 ↔
      arrivalForPoissonAE τ n ω ≤ t ∧
        t < arrivalForPoissonAE τ (n + 1) ω := by
    constructor
    · intro hc
      have hmem : t < arrivalForPoissonAE τ (n + 1) ω := by
        have hh : sInf {k : ℕ | t < arrivalForPoissonAE τ k ω} ∈
            {k : ℕ | t < arrivalForPoissonAE τ k ω} :=
          Nat.sInf_mem hnonempty
        change t < arrivalForPoissonAE τ
          (countForPoissonAE τ t ω) ω at hh
        rw [hc] at hh
        exact hh
      have hn : ¬ t < arrivalForPoissonAE τ n ω := by
        have hlt : n < sInf {k : ℕ | t < arrivalForPoissonAE τ k ω} := by
          change n < countForPoissonAE τ t ω
          rw [hc]
          exact Nat.lt_succ_self n
        exact Nat.notMem_of_lt_sInf hlt
      exact ⟨le_of_not_gt hn, hmem⟩
    · rintro ⟨hn, hs⟩
      apply Nat.le_antisymm
      · change sInf {k : ℕ | t < arrivalForPoissonAE τ k ω} ≤ n + 1
        exact Nat.sInf_le hs
      · change n + 1 ≤ countForPoissonAE τ t ω
        by_contra h
        have hle : countForPoissonAE τ t ω ≤ n :=
          Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)
        have hmem : t < arrivalForPoissonAE τ (countForPoissonAE τ t ω) ω := by
          have hh : sInf {k : ℕ | t < arrivalForPoissonAE τ k ω} ∈
              {k : ℕ | t < arrivalForPoissonAE τ k ω} :=
            Nat.sInf_mem hnonempty
          simpa [countForPoissonAE] using hh
        exact (not_lt_of_ge hn) (lt_of_lt_of_le hmem (hm hle))
  change (countForPoissonAE τ t ω = n + 1) =
    (t < arrivalForPoissonAE τ (n + 1) ω ∧
      ¬ t < arrivalForPoissonAE τ n ω)
  exact propext (by simpa only [not_lt] using
    (hiff.trans (and_comm)))

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ)
    (hdiv : ∀ᵐ ω ∂P, Tendsto (fun k =>
      arrivalForPoissonAE τ k ω) atTop atTop)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun k =>
      arrivalForPoissonAE τ k ω)) :
    {ω | countForPoissonAE τ t ω = n + 1} =ᵐ[P]
      ({ω | t < arrivalForPoissonAE τ (n + 1) ω} \
       {ω | t < arrivalForPoissonAE τ n ω}) := by
  exact positive_count_cylinder_ae τ t n hdiv hmono
