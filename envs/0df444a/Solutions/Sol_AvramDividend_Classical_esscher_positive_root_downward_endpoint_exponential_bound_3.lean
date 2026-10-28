-- Prove2me | solution 3 for AvramDividend.Classical.esscher_positive_root_downward_endpoint_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:16:35.647048+00:00
-- url     : https://prove2.me/submissions/ab1d81d2-4302-4226-90a2-07332df95ed0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_downward_endpoint_chernoff_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp ((φ / 2) * b)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))
        {ω : Ω | X.X t ω ≤ -b} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) * q / 2)) := by
  have hh : 0 < φ / 2 := by linarith
  have hhalf : φ / 2 ≤ φ := by linarith
  have hsec := levy_psi_positive_secant_monotone X
    (φ / 2) φ hh hhalf
  have hprod : X.ψ (φ / 2) ≤ (X.ψ φ / φ) * (φ / 2) :=
    (div_le_iff₀ hh).mp hsec
  have hmul : (q / φ) * (φ / 2) = q / 2 := by
    field_simp
  have hbound : X.ψ (φ / 2) ≤ q / 2 := by
    calc
      X.ψ (φ / 2) ≤ (X.ψ φ / φ) * (φ / 2) := hprod
      _ = q / 2 := by rw [hroot]; exact hmul
  have hmark := chat04_esscher_finite_downward_endpoint_chernoff_bound
    X t φ (φ / 2) b (le_of_lt hφ) hh hhalf
  have hshift : φ - φ / 2 = φ / 2 := by ring
  have ht : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hneg : (t : ℝ) * (X.ψ (φ - φ / 2) - X.ψ φ) ≤
      -(t : ℝ) * q / 2 := by
    rw [hshift, hroot]
    have hx := mul_le_mul_of_nonneg_left hbound ht
    nlinarith
  have hexp : ENNReal.ofReal
      (Real.exp ((t : ℝ) * (X.ψ (φ - φ / 2) - X.ψ φ))) ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) * q / 2)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hneg)
  exact le_trans hmark hexp
