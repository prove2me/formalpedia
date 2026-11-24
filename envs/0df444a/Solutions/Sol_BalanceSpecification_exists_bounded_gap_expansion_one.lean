-- Prove2me | solution 1 for BalanceSpecification.exists_bounded_gap_expansion_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:28.464148+00:00
-- url     : https://prove2.me/submissions/fe45ed2b-def5-46e3-abb7-156c5cdf0d87

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Theorems.Thm_BalanceSpecification_exists_bounded_gap_beta_digits
public import Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_of_uniform_right_completion


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2) :
    ∃ S : Set ℕ, 0 ∈ S ∧ HasBoundedSuccessiveGaps S ∧
      (∑' s : S, (β ^ (s.val + 1))⁻¹) = 1 := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ1
  have hden : 0 < β - 1 := sub_pos.mpr hβ1
  have hsmall : β - 1 < 1 / (β - 1) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith only [hβ1, hβ2, sq_nonneg (β - 1)]
  obtain ⟨d, hd, ⟨N, hN⟩, hsum⟩ :=
    exists_bounded_gap_beta_digits hβ1 hβ2 hden hsmall
  let e : ℕ → ℝ := fun n => match n with | 0 => 1 | k + 1 => d k
  have he n : e n = 0 ∨ e n = 1 := by
    cases n with
    | zero => exact Or.inr rfl
    | succ n => exact hd n
  have hnext : ∀ t : ℕ, ∃ s : ℕ, t ≤ s ∧ s ≤ t + N ∧ e s = 1 := by
    intro t
    cases t with
    | zero => exact ⟨0, le_refl _, Nat.zero_le _, rfl⟩
    | succ t =>
      obtain ⟨s, hts, hst, hs⟩ := hN t
      exact ⟨s + 1, by omega, by omega, hs⟩
  have heSum : HasSum (fun n : ℕ => e n / β ^ (n + 1)) 1 := by
    have htail : HasSum (fun n : ℕ => e (n + 1) / β ^ (n + 1 + 1))
        ((β - 1) / β) := by
      refine (hsum.div_const β).congr_fun (fun n => ?_)
      change d n / β ^ (n + 1 + 1) = (d n / β ^ (n + 1)) / β
      rw [div_div, pow_succ]
    have H : HasSum (fun n : ℕ => e n / β ^ (n + 1))
        (e 0 / β ^ (0 + 1) + (β - 1) / β) :=
      HasSum.zero_add (f := fun n : ℕ => e n / β ^ (n + 1)) htail
    have hvalue : e 0 / β ^ (0 + 1) + (β - 1) / β = 1 := by
      simp only [e, zero_add, pow_one]
      field_simp
      ring
    simpa only [hvalue] using H
  let S : Set ℕ := {n | e n = 1}
  have hS : HasBoundedSuccessiveGaps S := by
    apply hasBoundedSuccessiveGaps_of_uniform_right_completion
    refine ⟨N, ?_⟩
    intro t _
    obtain ⟨s, hts, hst, hs⟩ := hnext t
    exact ⟨s, hs, hts, hst⟩
  refine ⟨S, rfl, hS, ?_⟩
  calc
    (∑' s : S, (β ^ (s.val + 1))⁻¹) = ∑' n : ℕ, e n / β ^ (n + 1) := by
      rw [tsum_subtype S (fun n : ℕ => (β ^ (n + 1))⁻¹)]
      apply tsum_congr
      intro n
      by_cases hn : n ∈ S
      · have hn' : e n = 1 := hn
        simp only [Set.indicator_of_mem hn, hn', one_div]
      · have hn' : e n = 0 := (he n).resolve_right hn
        simp only [Set.indicator_of_notMem hn, hn', zero_div]
    _ = 1 := heSum.tsum_eq
end BalanceSpecification
