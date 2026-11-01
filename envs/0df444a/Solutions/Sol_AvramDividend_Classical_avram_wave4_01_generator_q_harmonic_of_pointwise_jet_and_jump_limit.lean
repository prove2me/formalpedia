-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_generator_q_harmonic_of_pointwise_jet_and_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:49:14.121498+00:00
-- url     : https://prove2.me/submissions/25bca350-e4f8-47b3-9c84-b1ee37407f04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact compensated Lévy generator equation is closed under pointwise
value, two-jet and full nonlocal jump-integral convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (f : ℝ → ℝ) (fn : ℕ → ℝ → ℝ)
    (hint : X.GeneratorIntegrable f x)
    (hval : Tendsto (fun n : ℕ => fn n x) atTop (nhds (f x)))
    (hfirst : Tendsto (fun n : ℕ => deriv (fn n) x)
      atTop (nhds (deriv f x)))
    (hsecond : Tendsto (fun n : ℕ => iteratedDeriv 2 (fn n) x)
      atTop (nhds (iteratedDeriv 2 f x)))
    (hjump : Tendsto
      (fun n : ℕ => ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (fn n) x y ∂X.ν)
      atTop
      (nhds (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand f x y ∂X.ν)))
    (hharm : ∀ n : ℕ,
      X.generator (fn n) x - q * fn n x = 0) :
    X.GeneratorIntegrable f x ∧
      X.generator f x - q * f x = 0 := by
  refine ⟨hint, ?_⟩
  have hgauss : Tendsto
      (fun n : ℕ => (X.σ ^ 2 / 2) * iteratedDeriv 2 (fn n) x)
      atTop
      (nhds ((X.σ ^ 2 / 2) * iteratedDeriv 2 f x)) :=
    tendsto_const_nhds.mul hsecond
  have hdrift : Tendsto
      (fun n : ℕ => X.c * deriv (fn n) x)
      atTop
      (nhds (X.c * deriv f x)) :=
    tendsto_const_nhds.mul hfirst
  have hgen : Tendsto
      (fun n : ℕ => X.generator (fn n) x)
      atTop (nhds (X.generator f x)) := by
    change Tendsto
      (fun n : ℕ =>
        (X.σ ^ 2 / 2) * iteratedDeriv 2 (fn n) x +
        X.c * deriv (fn n) x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand (fn n) x y ∂X.ν))
      atTop
      (nhds ((X.σ ^ 2 / 2) * iteratedDeriv 2 f x +
        X.c * deriv f x +
        (∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand f x y ∂X.ν)))
    exact (hgauss.add hdrift).add hjump
  have hresidual : Tendsto
      (fun n : ℕ => X.generator (fn n) x - q * fn n x)
      atTop
      (nhds (X.generator f x - q * f x)) :=
    hgen.sub (tendsto_const_nhds.mul hval)
  have hzero :
      (fun n : ℕ => X.generator (fn n) x - q * fn n x) =
        (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact hharm n
  rw [hzero] at hresidual
  exact tendsto_nhds_unique hresidual tendsto_const_nhds
