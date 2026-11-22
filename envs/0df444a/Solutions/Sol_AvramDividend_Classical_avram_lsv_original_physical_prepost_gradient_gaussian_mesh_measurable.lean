-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:37:19.37358+00:00
-- url     : https://prove2.me/submissions/5df752c6-edce-4baf-aede-0ae480cb30e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Elinear : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * |deriv w ypost - deriv w ypre| * |Z|
    ∀ m : ℕ, Measurable (Elinear m) := by
  intro Elinear m
  have hρm : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hX (s : ℝ≥0) : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hRm (s : ℝ≥0) : Measurable (rightLimit D s) :=
    ((dividendStrategy_rightLimit_adapted_rightCont D hD) s).mono
      (𝓕.rightCont.le s) le_rfl
  dsimp [Elinear]
  apply Finset.measurable_sum
  intro i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  have hz : Measurable (fun ω => X.X (s+Δ) ω - X.X s ω - (Δ : ℝ)*X.c) :=
    ((hX (s+Δ)).sub (hX s)).sub measurable_const
  have hpre : Measurable (fun ω => riskProcess X x D s ω) :=
    riskProcess_measurable X x D hD s
  have hpost : Measurable (fun ω => x + X.X s ω - rightLimit D s ω) :=
    (measurable_const.add (hX s)).sub (hRm s)
  have he : MeasurableSet {ω : Ω | s < ρ ω} :=
    measurableSet_lt measurable_const hρm
  have hwgt : Measurable (fun ω =>
      if s < ρ ω then Real.exp (-(q*(s:ℝ))) else 0) :=
    Measurable.ite he measurable_const measurable_const
  exact (hwgt.abs.mul
    (((measurable_deriv w).comp hpost).sub
      ((measurable_deriv w).comp hpre)).abs).mul hz.abs
