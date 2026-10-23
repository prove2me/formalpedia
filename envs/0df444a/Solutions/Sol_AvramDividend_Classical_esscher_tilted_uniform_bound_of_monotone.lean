-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_uniform_bound_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:06:29.87078+00:00
-- url     : https://prove2.me/submissions/551829e1-e309-4f77-87a2-f1b37e3fecfb

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
import Theorems.Thm_AvramDividend_Classical_monotone_exp_laplace_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x → V x ≤ Real.exp 2 * (φ / q) := by
  have hnonneg : ∀ y : ℝ, 0 < y → 0 ≤ V y := by
    intro y hy
    rw [hV y hy]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hW.2.1 y (le_of_lt hy))
  have hLap : ∀ θ : ℝ, 0 < θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) ≤
      (φ / q) / θ := by
    intro θ hθ
    have hgap : (q / φ) * θ ≤ X.ψ (φ + θ) - q :=
      levy_psi_root_shifted_increment_lower X q φ θ hq hφ hθ hroot
    have hgap_pos : 0 < X.ψ (φ + θ) - q :=
      lt_of_lt_of_le (mul_pos (div_pos hq hφ) hθ) hgap
    have hψ : q < X.ψ (θ + φ) := by
      rw [add_comm θ φ]
      linarith
    obtain ⟨hint, heq⟩ := esscher_tilted_scale_laplace_shift
      X q W hW φ θ (by linarith) hψ
    have hEq : EqOn
        (fun y : ℝ => Real.exp (-(θ * y)) *
          (Real.exp (-(φ * y)) * W y))
        (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) := by
      intro y hy
      change Real.exp (-(θ * y)) * (Real.exp (-(φ * y)) * W y) =
        Real.exp (-(θ * y)) * V y
      rw [hV y hy]
    have hintV : IntegrableOn
        (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume :=
      hint.congr_fun hEq measurableSet_Ioi
    have heqV :
        (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
        (X.ψ (θ + φ) - q)⁻¹ := by
      calc
        _ = (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
            (Real.exp (-(φ * y)) * W y) ∂volume) :=
          setIntegral_congr_fun measurableSet_Ioi hEq.symm
        _ = (X.ψ (θ + φ) - q)⁻¹ := heq
    have hrec :
        (X.ψ (θ + φ) - q)⁻¹ ≤ (φ / q) / θ := by
      have hbase :
          1 / (X.ψ (φ + θ) - q) ≤ 1 / ((q / φ) * θ) :=
        one_div_le_one_div_of_le (mul_pos (div_pos hq hφ) hθ) hgap
      have hident : 1 / ((q / φ) * θ) = (φ / q) / θ := by
        field_simp
      calc
        _ = 1 / (X.ψ (φ + θ) - q) := by rw [add_comm φ θ]; ring
        _ ≤ 1 / ((q / φ) * θ) := hbase
        _ = (φ / q) / θ := hident
    exact ⟨hintV, heqV ▸ hrec⟩
  exact monotone_exp_laplace_uniform_bound
    V (φ / q) (le_of_lt (div_pos hφ hq)) hnonneg hmono hLap
