-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_genuine_strip_from_indep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:52:49.67504+00:00
-- url     : https://prove2.me/submissions/c4642911-1af5-4649-9c24-59bbe735014f

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_real_mgf_rate_gap
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_independent_real_mgf_crossmul
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
    (hIndep : IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) :
    ∀ β : ℝ, 0 < β → β < lam →
      mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β *
      (p - (X.ψ (φ + β) - q)) =
      (p / lam) * (lam - β) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
  let S : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ :=
    fun z => runningSup X (Real.toNNReal z.2) z.1 -
      X.X (Real.toNNReal z.2) z.1
  have hSMeas : Measurable S :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hDMeas : Measurable D :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hi : IndepFun S D μ := hIndep
  intro β hβ hβlam
  have hMono := esscher_levy_shift_strictMonoOn X q φ hq hφ hroot
  have hGap : X.ψ (φ + β) - q < p := by
    have hb : β ∈ Ici (0 : ℝ) := hβ.le
    have hl : lam ∈ Ici (0 : ℝ) := hlam.le
    have hh := hMono hb hl hβlam
    simpa only [hlamroot] using hh
  have hSup :
      mgf S μ β = lam / (lam - β) := by
    simpa only [S, μ] using
      (avram_ws01e_bf_new_tilted_supremum_real_mgf_rate_gap
        X φ q p lam β hφ hq hroot hp hlam hlamroot hβlam)
  have hTerminal :
      mgf (fun z : Ω × ℝ => S z - D z) μ β =
      p / (p - (X.ψ (φ + β) - q)) := by
    have hEq : (fun z : Ω × ℝ => S z - D z) =
        (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) := by
      funext z
      dsimp [S, D]
      ring
    rw [hEq]
    simpa only [μ] using
      (avram_ws01e_bf_new_true_terminal_real_mgf_rate_gap
        X φ q p β hφ hq hroot hp hβ.le hGap hJoint)
  have hCross :=
    avram_ws01e_bf_new_independent_real_mgf_crossmul
      S D p lam β (X.ψ (φ + β) - q)
      hi hSMeas hDMeas hGap hβlam hSup hTerminal
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hReal :
      mgf (fun z : Ω × ℝ => -D z) μ β *
        (p - (X.ψ (φ + β) - q)) =
      (p / lam) * (lam - β) := by
    have hDiv :
        mgf (fun z : Ω × ℝ => -D z) μ β *
          (p - (X.ψ (φ + β) - q)) =
        (p * (lam - β)) / lam := by
      apply (eq_div_iff hlamne).2
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hCross
    calc
      _ = (p * (lam - β)) / lam := hDiv
      _ = (p / lam) * (lam - β) := by ring
  simpa only [S, D, μ] using hReal
