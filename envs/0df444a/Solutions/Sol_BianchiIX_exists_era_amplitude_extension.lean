-- Prove2me | solution 1 for BianchiIX.exists_era_amplitude_extension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:44:15.418676+00:00
-- url     : https://prove2.me/submissions/b76f3065-f433-47bc-b70f-8af25ea50a34

import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_era_interval_inverse
import Theorems.Thm_BianchiIX_exists_era_output_graph_estimates
import Theorems.Thm_BianchiIX_extension_amplitude_gain
import Theorems.Thm_BianchiIX_intervalRadiusInverse_control
import Theorems.Thm_BianchiIX_radiusAmplitude_window_extension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
open BianchiIX
open Set



/-- The selected actual era curve has a canonical positive C1 extension with the next amplitude budget. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        let g := intervalRadiusInverse φ a b
        let k := eraGraphRadius η J m U W
        let u₀ := eraGraphWall η J m U W 1
        let w₀ := eraGraphWall η J m U W 3
        let u := eraAmplitudeExtension η J m β U W 1
        let w := eraAmplitudeExtension η J m β U W 3
        C * B ^ (7 / 24 : ℝ) < 1 / 2 ∧ ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
        (∀ y ∈ Icc (2 * β) (1 - 2 * β), k (g y) = 2 / y ∧
          u (2 / y) = u₀ (g y) ∧ w (2 / y) = w₀ (g y) ∧
          deriv u (2 / y) = deriv u₀ (g y) / deriv k (g y) ∧
          deriv w (2 / y) = deriv w₀ (g y) / deriv k (g y)) ∧
        ∀ t : ℝ, 0 < u t ∧ 0 < w t ∧ u t + w t ≤ B ^ (4 / 3 : ℝ) ∧
          |deriv u t| ≤ (C * B ^ (7 / 24 : ℝ)) * Real.sqrt (u t) ∧
          |deriv w t| ≤ (C * B ^ (7 / 24 : ℝ)) * Real.sqrt (w t) := by
  obtain ⟨δi, hδi, hδimax, HI⟩ := exists_era_interval_inverse
  obtain ⟨δo, hδo, _, HO⟩ := exists_era_output_graph_estimates
  refine ⟨min δi δo, lt_min hδi hδo, (min_le_left _ _).trans hδimax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εi, hεi, hεimax, Ci, hCi, HEI⟩ := HI η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨εo, hεo, _, Co, hCo, HEO⟩ := HO η hη (hηδ.trans (min_le_right _ _)) J hJ
  let C := Ci + Co
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hCiC : Ci ≤ C := by dsimp [C]; linarith
  have hCoC : Co ≤ C := by dsimp [C]; linarith
  obtain ⟨ε, hε, hεmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 2) Finset.univ
    (C := ![C, (25 / 16) * C]) (p := ![7 / 24, 17 / 30]) (ε := ![1 / 2, 1])
    (by intro i _; fin_cases i <;> dsimp <;> positivity)
    (by intro i _; fin_cases i <;> norm_num)
    (by intro i _; fin_cases i <;> norm_num) (lt_min hεi hεo)
  have hεi' : ε ≤ εi := hεmax.le.trans (min_le_left _ _)
  have hεo' : ε ≤ εo := hεmax.le.trans (min_le_right _ _)
  refine ⟨ε, hε, hεi'.trans hεimax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph φ g k u₀ w₀ u w
  have hab : a < b := by dsimp [a, b]; linarith
  have hB : 0 < B := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph a ⟨le_rfl, hab.le⟩
    linarith
  have hbε : B ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le
    (pow_le_one₀ (half_pos hβ).le (by linarith)))
  have hconeBudget : C * B ^ (7 / 24 : ℝ) < 1 / 2 := Hbudget B ⟨hB, hbε⟩ 0 (Finset.mem_univ _)
  have hextBudget : (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) ≤ 1 :=
    (Hbudget B ⟨hB, hbε⟩ 1 (Finset.mem_univ _)).le
  have hcontract := extension_amplitude_gain hB le_rfl hC0 hextBudget
  have hpow {e : ℝ} (he : ε ≤ e) : B ≤ e * (β / 2) ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right he (pow_nonneg (half_pos hβ).le _))
  obtain ⟨_, _, hfa, hfb, Hinv⟩ := HEI m β B U W hβ hβmax (hscale.trans hεi') (hpow hεi')
    ((mul_le_mul_of_nonneg_right hCiC hB.le).trans_lt hmargin) Hgraph
  change φ a < 2 * β at hfa
  change 1 - 2 * β < φ b at hfb
  have Hout := HEO m β B U W hβ hβmax (hscale.trans hεo') (hpow hεo')
    ((mul_le_mul_of_nonneg_right hCoC hB.le).trans_lt hmargin) Hgraph
  have Hk (r : ℝ) (hr : r ∈ Icc a b) : ContDiffAt ℝ 1 k r := (Hout r hr).1
  have Hkd (r : ℝ) (hr : r ∈ Icc a b) : deriv k r < 0 := (Hout r hr).2.1
  have hba := (intervalRadiusInverse_control hab Hk Hkd).1
  have hφ (r : ℝ) : φ r = 2 / k r := rfl
  have hden : 0 < 1 - 2 * β := by linarith
  have hkb : 0 < k b := by
    by_contra! hn
    have Hnon := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hn
    rw [← hφ b] at Hnon
    linarith
  have hka : 0 < k a := hkb.trans hba
  let l := 2 / (1 - 2 * β)
  let r := 1 / β
  have hlr : l < r := (div_lt_div_iff₀ hden hβ).mpr (by nlinarith)
  have hkl : k b < l := by
    have H := (lt_div_iff₀ hkb).mp (hφ b ▸ hfb)
    exact (lt_div_iff₀ hden).mpr (by nlinarith)
  have hkr : r < k a := by
    have H := (div_lt_iff₀ hka).mp (hφ a ▸ hfa)
    exact (div_lt_iff₀ hβ).mpr (by nlinarith)
  have hwindow : Icc l r ⊆ Icc (k b) (k a) := fun _ hx =>
    ⟨hkl.le.trans hx.1, hx.2.trans hkr.le⟩
  have hcoef (p : ℝ) : Co * B ^ p ≤ C * B ^ p :=
    mul_le_mul_of_nonneg_right hCoC (Real.rpow_nonneg hB.le _)
  obtain ⟨Hcu, Hcw, Hmatch, Hbounds⟩ := radiusAmplitude_window_extension hab hlr hwindow
    (by linarith : C * B ^ (7 / 24 : ℝ) ≤ 1) Hk Hkd
    (fun x hx => (Hout x hx).2.2.1) (fun x hx => (Hout x hx).2.2.2.1)
    (fun x hx => (Hout x hx).2.2.2.2.1) (fun x hx => (Hout x hx).2.2.2.2.2.1)
    (fun x hx => (Hout x hx).2.2.2.2.2.2.2.1.trans
      (mul_le_mul_of_nonneg_right (hcoef _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))))
    (fun x hx => (Hout x hx).2.2.2.2.2.2.2.2.trans
      (mul_le_mul_of_nonneg_right (hcoef _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))))
    (fun x hx => (Hout x hx).2.2.2.2.2.2.1.trans (hcoef _))
  refine ⟨hconeBudget, Hcu, Hcw, ?_, ?_⟩
  · intro y hy
    obtain ⟨hgi, hfg, _⟩ := Hinv y hy
    change φ (g y) = y at hfg
    have hgc : g y ∈ Icc a b := ⟨hgi.1.le, hgi.2.le⟩
    have hky : k (g y) = 2 / y := by
      calc
        _ = 2 / (2 / k (g y)) := by field_simp
        _ = 2 / φ (g y) := by rw [hφ]
        _ = _ := by rw [hfg]
    have hy0 : 0 < y := (mul_pos (by norm_num) hβ).trans_le hy.1
    have hywin : 2 / y ∈ Icc l r :=
      ⟨div_le_div_of_nonneg_left (by norm_num) hy0 hy.2,
        (div_le_div_iff₀ hy0 hβ).mpr (by simpa using hy.1)⟩
    have H := Hmatch (g y) hgc (by rwa [hky])
    rw [hky] at H
    exact ⟨hky, H⟩
  · intro t
    obtain ⟨hu, hw, hsum, hdu, hdw⟩ := Hbounds t
    exact ⟨hu, hw, hsum.trans hcontract, hdu, hdw⟩
