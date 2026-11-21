-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_gaussian_prepost_explicit_twojet_envelope_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:14:09.050312+00:00
-- url     : https://prove2.me/submissions/4de8e24a-d56c-46a9-a7f8-ebfb93b67796

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- True original controlled Gaussian Hermite pre/post sum difference
admits a pathwise weighted gradient and Hessian cell error envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then
            let y := riskProcess X x D s ω
            let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
            Real.exp (-(q * (s : ℝ))) *
              (deriv w y * Z +
                (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0
    let N : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * Z +
              (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * (|deriv w ypost - deriv w ypre| * |Z| +
          |iteratedDeriv 2 w ypost / 2 - iteratedDeriv 2 w ypre / 2| * |U|)
    ∀ m : ℕ, ∀ ω : Ω, |N m ω - M m ω| ≤ E m ω := by
  intro M N E m ω
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let z : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
  let u : ℕ → ℝ := fun i => z i ^ 2 - (Δ : ℝ) * X.σ ^ 2
  let e : ℕ → ℝ := fun i => if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) else 0
  let a : ℕ → ℝ := fun i => deriv w (x + X.X (s i) ω - rightLimit D (s i) ω)
  let b : ℕ → ℝ := fun i => iteratedDeriv 2 w (x + X.X (s i) ω - rightLimit D (s i) ω) / 2
  let c : ℕ → ℝ := fun i => deriv w (riskProcess X x D (s i) ω)
  let d : ℕ → ℝ := fun i => iteratedDeriv 2 w (riskProcess X x D (s i) ω) / 2
  have hN : N m ω = ∑ i ∈ Finset.range m, e i * (a i * z i + b i * u i) := by
    simp only [N, e, a, b, z, u, s, Δ]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hM : M m ω = ∑ i ∈ Finset.range m, e i * (c i * z i + d i * u i) := by
    simp only [M, e, c, d, z, u, s, Δ]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have hE : E m ω =
      ∑ i ∈ Finset.range m, |e i| *
        (|a i - c i| * |z i| + |b i - d i| * |u i|) := by
    rfl
  have hsplit : N m ω - M m ω =
      ∑ i ∈ Finset.range m, e i *
        ((a i * z i + b i * u i) - (c i * z i + d i * u i)) := by
    rw [hN, hM, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    |N m ω - M m ω| =
      |∑ i ∈ Finset.range m, e i *
        ((a i * z i + b i * u i) - (c i * z i + d i * u i))| := by rw [hsplit]
    _ ≤ ∑ i ∈ Finset.range m, |e i| *
        (|a i - c i| * |z i| + |b i - d i| * |u i|) :=
      avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope m e z u a b c d
    _ = E m ω := hE.symm
