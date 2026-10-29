-- Prove2me | solution 1 for AvramDividend.Classical.levy_infinite_jump_positive_factor_witnesses_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:56:47.903775+00:00
-- url     : https://prove2.me/submissions/b25cca05-eacb-4b77-bbad-df314515aeba

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∃ q φ p lam m : ℝ,
      0 < q ∧ 0 < φ ∧ X.ψ φ = q ∧
      0 < p ∧ 0 < lam ∧ X.ψ (φ + lam) - q = p ∧
      0 < m ∧ HasDerivAt X.ψ m (φ + lam) := by
  obtain ⟨φ, hφ1, hlarge⟩ :=
    psi_normalised_unbounded_small_jumps X hσ hjump 1
  have hφ : 0 < φ := by linarith
  have hratio : 1 < X.ψ φ / φ := hlarge φ le_rfl
  have hq : 0 < X.ψ φ := by
    have hh := (lt_div_iff₀ hφ).mp hratio
    nlinarith
  have hpLower :=
    levy_psi_root_shifted_increment_lower
      X (X.ψ φ) φ φ hq hφ hφ rfl
  have hp : 0 < X.ψ (φ + φ) - X.ψ φ :=
    lt_of_lt_of_le (mul_pos (div_pos hq hφ) hφ) hpLower
  obtain ⟨m, hderiv⟩ :=
    avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
      X (φ + φ) (by linarith)
  have hq2 : 0 < X.ψ (φ + φ) := by linarith
  have hm : 0 < m :=
    (esscher_levy_positive_root_derivative_lower
      X (X.ψ (φ + φ)) (φ + φ) m hq2 (by linarith)
      rfl hderiv).2
  exact ⟨X.ψ φ, φ, X.ψ (φ + φ) - X.ψ φ, φ, m,
    hq, hφ, rfl, hp, hφ, rfl, hm, hderiv⟩
