-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_drawdown_inverse_factor_all_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:53:50.859892+00:00
-- url     : https://prove2.me/submissions/869d876f-0cab-4da3-b378-ec51dbf08992

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Inverse Esscher weighting factorises the original-clock drawdown
transform at every real parameter, including potentially infinite moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p β : ℝ) (hφ : 0 ≤ φ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    ENNReal.ofReal p *
      (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
        ∂(P.prod (expMeasure (p + q)))) =
    ENNReal.ofReal (p + q) *
      ((∫⁻ z, ENNReal.ofReal (Real.exp (-φ * S z)) ∂Qp) *
       (∫⁻ z, ENNReal.ofReal (Real.exp (-(β - φ) * D z)) ∂Qp)) := by
  classical
  let Qp : Measure (Ω × ℝ) :=
    (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
  let S : Ω × ℝ → ℝ := fun z =>
    runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z =>
    S z - X.X (Real.toNNReal z.2) z.1
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-φ * s))
  let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(β - φ) * x))
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hS : Measurable S := by
    simpa only [S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D := by
    simpa only [D, S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hInd : IndepFun S D Qp :=
    avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
      X φ p hφ hp hJoint
  have hFact :
      (∫⁻ z, f (S z) * g (D z) ∂Qp) =
      (∫⁻ z, f (S z) ∂Qp) * (∫⁻ z, g (D z) ∂Qp) := by
    have hTest : IndepFun (f ∘ S) (g ∘ D) Qp := hInd.comp hf hg
    change (∫⁻ z, (f ∘ S) z * (g ∘ D) z ∂Qp) =
      (∫⁻ z, (f ∘ S) z ∂Qp) * (∫⁻ z, (g ∘ D) z ∂Qp)
    exact ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (hf.comp hS) (hg.comp hD) hTest
  have hPath (z : Ω × ℝ) :
      ENNReal.ofReal (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)) *
        ENNReal.ofReal (Real.exp (-β * D z)) =
      f (S z) * g (D z) := by
    have hReal : -φ * X.X (Real.toNNReal z.2) z.1 + -β * D z =
        -φ * S z + -(β - φ) * D z := by
      dsimp [D]
      ring
    calc
      _ = ENNReal.ofReal (Real.exp
          (-φ * X.X (Real.toNNReal z.2) z.1 + -β * D z)) := by
          rw [Real.exp_add]
          exact (ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))).symm
      _ = ENNReal.ofReal (Real.exp (-φ * S z + -(β - φ) * D z)) := by
          rw [hReal]
      _ = f (S z) * g (D z) := by
          rw [Real.exp_add]
          exact ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
  have hW : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-β * D z))) := by fun_prop
  have hInverse := avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
    X φ q p hq hroot hp
    (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp (-β * D z))) hW
  calc
    ENNReal.ofReal p *
        (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z))
          ∂(P.prod (expMeasure (p + q)))) =
      ENNReal.ofReal (p + q) *
        (∫⁻ z, ENNReal.ofReal
          (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)) *
          ENNReal.ofReal (Real.exp (-β * D z)) ∂Qp) := by
          exact hInverse.symm
    _ = ENNReal.ofReal (p + q) *
        (∫⁻ z, f (S z) * g (D z) ∂Qp) := by
          congr 1
          exact lintegral_congr hPath
    _ = _ := by rw [hFact]
