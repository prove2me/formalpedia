-- Prove2me | solution 1 for AvramDividend.Classical.positive_infinite_kernel_exponential_deficit_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:34:35.285678+00:00
-- url     : https://prove2.me/submissions/0948c55d-84fe-4ebf-8873-852c412d254f

/-
Adapted from TauCeti/Probability/Distributions/Stable/Approximation/Basic.lean,
map_neg_stableCompensatedPoissonMeasure (reflection of Levy measures),
source commit 3832571c64482365836c2744324ee16230608f7f.
Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
The finite-measure reflection code is adapted to the arbitrary Levy measure,
using an existing independently Proved negative-jump divergence theorem.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_negative_levy_exponential_deficit_tendsto_top

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

noncomputable section

theorem solution
    (κ : Measure ℝ)
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ t : ℝ, ENNReal.ofReal
          (1 - Real.exp (-((n : ℝ) * t))) ∂κ)
      atTop (𝓝 (⊤ : ℝ≥0∞)) := by
  let ν : Measure ℝ := κ.map (fun t : ℝ => -t)
  have hpreSupp : (fun t : ℝ => -t) ⁻¹' Ici (0 : ℝ) = Iic 0 := by
    ext t
    simp
  have hνsupp : ν (Ici (0 : ℝ)) = 0 := by
    change (κ.map (fun t : ℝ => -t)) (Ici (0 : ℝ)) = 0
    rw [Measure.map_apply measurable_neg measurableSet_Ici, hpreSupp]
    exact hκsupp
  have hpos : κ (Ioi (0 : ℝ)) = ⊤ := by
    apply top_unique
    calc
      ⊤ = κ (Ioc (0 : ℝ) 1) := hκinf.symm
      _ ≤ κ (Ioi (0 : ℝ)) := measure_mono (by
        intro t ht
        exact ht.1)
  have hpreInf : (fun t : ℝ => -t) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
    ext t
    simp
  have hνinf : ν (Iio (0 : ℝ)) = ⊤ := by
    change (κ.map (fun t : ℝ => -t)) (Iio (0 : ℝ)) = ⊤
    rw [Measure.map_apply measurable_neg measurableSet_Iio, hpreInf]
    exact hpos
  have hrefl (n : ℕ) :
      (∫⁻ y : ℝ,
        ENNReal.ofReal (1 - Real.exp ((n : ℝ) * y)) ∂ν) =
      (∫⁻ t : ℝ,
        ENNReal.ofReal (1 - Real.exp (-((n : ℝ) * t))) ∂κ) := by
    have hf : Measurable
        (fun y : ℝ => ENNReal.ofReal (1 - Real.exp ((n : ℝ) * y))) := by
      fun_prop
    change
      (∫⁻ y : ℝ, ENNReal.ofReal
        (1 - Real.exp ((n : ℝ) * y)) ∂(κ.map (fun t : ℝ => -t))) = _
    rw [lintegral_map hf measurable_neg]
    congr 1
    funext t
    simp only [mul_neg]
  have hneg := AvramDividend.Classical.negative_levy_exponential_deficit_tendsto_top
    ν hνsupp hνinf
  simpa only [hrefl] using hneg
