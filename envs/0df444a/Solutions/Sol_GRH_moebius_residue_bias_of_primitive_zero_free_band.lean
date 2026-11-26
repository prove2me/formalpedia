-- Prove2me | solution 1 for GRH.moebius_residue_bias_of_primitive_zero_free_band
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:06:37.057679+00:00
-- url     : https://prove2.me/submissions/49b1b445-a39d-4ade-82dc-bda336a6ef53

import Theorems.Thm_GRH_reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs
import Theorems.Thm_GRH_nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith

private theorem primitive_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← χ.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]

private theorem lift_nonvanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor] (s : ℂ) (hs : 0 < s.re) (hz : χ.primitiveCharacter.LFunction s ≠ 0) :
    χ.LFunction s ≠ 0 := by
  have identity := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (s := s) (Or.inl (primitive_ne_one χ hχ))
  rw [χ.changeLevel_primitiveCharacter] at identity
  rw [identity]
  apply mul_ne_zero hz (Finset.prod_ne_zero_iff.mpr ?_)
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have decay : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos pp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast pp.one_lt) (by linarith)
  have hf : ‖χ.primitiveCharacter p * (p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.primitiveCharacter.norm_le_one _)).trans_lt decay
  intro zero
  rw [← sub_eq_zero.mp zero, norm_one] at hf
  exact lt_irrefl _ hf

theorem solution (q : ℕ) [NeZero q] (α σ : ℝ)
    (hα : (1/2:ℝ) ≤ α) (hcap : α ≤ (0.8749570698:ℝ)) (hσ : α < σ)
    (hz : ∀ (d : ℕ) [NeZero d], d ∣ q → ∀ ψ : DirichletCharacter ℂ d,
      ψ.IsPrimitive → ψ ≠ 1 → ∀ s : ℂ,
      α < s.re → s.re ≤ (0.8749570698:ℝ) → ψ.LFunction s ≠ 0) :
    ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ k ∈ Finset.range (N+1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) -
        (∑ k ∈ Finset.range (N+1), if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) /
          (q.totient : ℝ)| ≤ C * ((N : ℝ)+1)^σ := by
  apply (GRH.reduced_residue_bias_iff_nonprincipal_character_bounds_at_cutoffs q
    (fun k => (ArithmeticFunction.moebius k : ℝ)) id (fun N => ((N : ℝ)+1)^σ)).2
  intro χ hχ
  have hL (s : ℂ) (hs : α < s.re) : χ.LFunction s ≠ 0 := by
    by_cases h : s.re ≤ (0.8749570698:ℝ)
    · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      apply lift_nonvanishing χ hχ s (by linarith)
      apply hz χ.conductor χ.conductor_dvd_level χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive (primitive_ne_one χ hχ) s hs h
    · exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ (lt_of_not_ge h) (fun z => hχ z.1)
  have h1 : α ≤ 1 := by linarith
  obtain ⟨D, hD, h⟩ :=
    GRH.nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane q χ hχ α σ hα h1 hσ hL
  refine ⟨D, hD, fun N => ?_⟩
  simpa only [id_eq, Complex.ofReal_intCast] using h N
