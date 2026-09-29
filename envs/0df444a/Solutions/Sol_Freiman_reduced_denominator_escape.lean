-- Prove2me | solution 1 for Freiman.reduced_denominator_escape
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:53:10.991162+00:00
-- url     : https://prove2.me/submissions/8a656168-6f27-43be-a725-ccf090e77711

import Definitions.Def_Freiman_perronArithmetic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp

open Freiman Filter Topology

set_option autoImplicit false

private theorem approximation_tendsto (ξ : ℝ) :
    Tendsto (fun q : ℕ => (reducedApproximation ξ q : ℝ)) atTop (nhds ξ) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / ε)
  refine ⟨Q + 1, ?_⟩
  intro q hq
  have hqp : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hQq : (Q : ℝ) ≤ q := by exact_mod_cast (show Q ≤ q by omega)
  have hprod : 1 < (q : ℝ) * ε := (div_lt_iff₀ hε).mp (hQ.trans_le hQq)
  have hlo := Int.lt_floor_add_one ((q : ℝ) * ξ + 1 / 2)
  have hhi := Int.floor_le ((q : ℝ) * ξ + 1 / 2)
  rw [Real.dist_eq]
  simp only [reducedApproximation, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    nearestNumerator]
  apply abs_lt.mpr
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hqp]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hqp]
    nlinarith

theorem solution (ξ : ℝ) (hξ : Irrational ξ) :
    ∀ R : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → R ≤ reducedApproximationDenominator ξ q := by
  have havoid (R : ℕ) : ∀ᶠ q : ℕ in atTop, reducedApproximationDenominator ξ q ≠ R := by
    by_cases hR : R = 0
    · subst R
      exact Eventually.of_forall (fun q => (reducedApproximation ξ q).den_nz)
    · have hirr : Irrational ((R : ℝ) * ξ) := hξ.natCast_mul hR
      have hl : (Int.floor ((R : ℝ) * ξ) : ℝ) < (R : ℝ) * ξ :=
        lt_of_le_of_ne (Int.floor_le _) (hirr.ne_int _).symm
      have hu := Int.lt_floor_add_one ((R : ℝ) * ξ)
      have hlim : Tendsto (fun q : ℕ => (R : ℝ) * (reducedApproximation ξ q : ℝ))
          atTop (nhds ((R : ℝ) * ξ)) := tendsto_const_nhds.mul (approximation_tendsto ξ)
      have he := hlim.eventually (Ioo_mem_nhds hl hu)
      filter_upwards [he] with q hq
      intro hd
      have heq : (R : ℝ) * (reducedApproximation ξ q : ℝ) =
          ((reducedApproximation ξ q).num : ℝ) := by
        rw [Rat.cast_def]
        change (reducedApproximation ξ q).den = R at hd
        rw [hd]
        field_simp
      rw [heq] at hq
      have h₁ : Int.floor ((R : ℝ) * ξ) < (reducedApproximation ξ q).num := by
        exact_mod_cast hq.1
      have h₂ : (reducedApproximation ξ q).num < Int.floor ((R : ℝ) * ξ) + 1 := by
        exact_mod_cast hq.2
      omega
  intro R
  have he : ∀ᶠ q : ℕ in atTop, R ≤ reducedApproximationDenominator ξ q := by
    induction R with
    | zero => exact Eventually.of_forall (fun q => Nat.zero_le _)
    | succ R ih =>
      filter_upwards [ih, havoid R] with q hq hne
      omega
  exact eventually_atTop.mp he
