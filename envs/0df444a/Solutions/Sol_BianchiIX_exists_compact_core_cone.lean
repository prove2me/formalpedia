-- Prove2me | solution 1 for BianchiIX.exists_compact_core_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:56:05.408506+00:00
-- url     : https://prove2.me/submissions/ac0f96e5-1653-452b-9be5-bb03926b746a

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
import Theorems.Thm_BianchiIX_compactCoreFactor_transverse_differential
import Theorems.Thm_BianchiIX_exists_compact_core_factor_bounds
import Theorems.Thm_BianchiIX_exists_compact_core_radial_margin
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.wall_multiplier_cone_bound {u m du dℓ dout θ : ℝ} (hu : 0 ≤ u) (hm : 0 < m)
    (hdu : |du| ≤ θ * Real.sqrt u) (hd : dout = m * (du + u * dℓ)) :
    |dout| ≤ Real.sqrt (u * m) *
      (Real.sqrt m * θ + Real.sqrt m * Real.sqrt u * |dℓ|) := by
  rw [hd, abs_mul, abs_of_pos hm]
  calc
    _ ≤ m * (|du| + |u * dℓ|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hm.le
    _ ≤ m * (θ * Real.sqrt u + u * |dℓ|) := by
      rw [abs_mul, abs_of_nonneg hu]
      exact mul_le_mul_of_nonneg_left (add_le_add hdu (le_refl _)) hm.le
    _ = _ := by
      rw [Real.sqrt_mul hu]
      ring_nf
      rw [Real.sq_sqrt hm.le, Real.sq_sqrt hu]
      ring

end
end

/-- A fixed strict cone contraction holds on the compact reference segment, including zero walls. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ σ > (0 : ℝ), σ < 1 ∧
      ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε) → (0 ≤ Y 2 ∧ Y 2 ≤ ε) →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          let d := fderiv ℝ (coreReturnState coreRadiusReturnTime) Y v
          0 < d 0 ∧ ∀ i : Fin 2,
            |d i.succ| ≤ σ * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) * d 0 := by
  obtain ⟨εf, hεf, q, hq, hq1, L, hL, hf⟩ := exists_compact_core_factor_bounds
  let s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs1 : s < 1 := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq.le hq1
  let e := (1 - s) / 4
  have he : 0 < e := by dsimp [e]; linarith only [hs1]
  have he4 : e < 1 / 4 := by dsimp [e]; linarith only [hs]
  have hse : s + 4 * e = 1 := by dsimp [e]; ring
  obtain ⟨εr, hεr, R, hR, hr⟩ := exists_compact_core_radial_margin he
  let b := e / (1 + R + L)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbudget : (1 + R + L) * b = e := by dsimp [b]; field_simp
  let ε := min εf (min εr (min 1 (b ^ 2)))
  have hε : 0 < ε := lt_min hεf (lt_min hεr (lt_min zero_lt_one (sq_pos_of_pos hb)))
  have hεf' : ε ≤ εf := min_le_left _ _
  have hεr' : ε ≤ εr := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε ≤ b ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hseb : Real.sqrt ε ≤ b := (Real.sqrt_le_iff).mpr ⟨hb.le, hεb⟩
  have hLe : L * Real.sqrt ε ≤ e := by
    have H := mul_le_mul_of_nonneg_left hseb hL.le
    nlinarith only [H, hbudget, hb.le, mul_nonneg hR.le hb.le]
  have hRe : R * Real.sqrt ε ≤ e := by
    have H := mul_le_mul_of_nonneg_left hseb hR.le
    nlinarith only [H, hbudget, hb.le, mul_nonneg hL.le hb.le]
  have hσ : 0 < 1 - e := by linarith only [he4]
  refine ⟨ε, hε, 1 - e, hσ, by linarith only [he], ?_⟩
  intro Y hk hu hw
  have habsu : |Y 1| ≤ ε := (abs_of_nonneg hu.1).le.trans hu.2
  have habsw : |Y 2| ≤ ε := (abs_of_nonneg hw.1).le.trans hw.2
  obtain ⟨hvalid, hF, hfac⟩ := hf Y hk (habsu.trans hεf') (habsw.trans hεf')
  obtain ⟨hrad, hnorm⟩ := hr Y hk (habsu.trans hεr') (habsw.trans hεr')
  refine ⟨hvalid, hF, ?_⟩
  intro v hv ha hb'
  let D := fderiv ℝ (coreReturnState coreRadiusReturnTime) Y
  let v₀ : CoreAngleState := Pi.single 0 1
  have hsu := Real.sqrt_le_sqrt hu.2
  have hsw := Real.sqrt_le_sqrt hw.2
  have hse1 : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr hε1
  have hvnorm : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i
    · simp [hv]
    · exact ha.trans (hsu.trans hse1)
    · exact hb'.trans (hsw.trans hse1)
  have hdiff : ‖v - v₀‖ ≤ Real.sqrt ε := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    fin_cases i
    · simp [v₀, hv, Real.sqrt_nonneg]
    · simpa [v₀] using ha.trans hsu
    · simpa [v₀] using hb'.trans hsw
  have herror : |D (v - v₀) 0| ≤ e := by
    calc
      _ ≤ ‖D (v - v₀)‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (D (v - v₀)) 0
      _ ≤ ‖D‖ * ‖v - v₀‖ := D.le_opNorm _
      _ ≤ R * Real.sqrt ε := mul_le_mul hnorm hdiff (norm_nonneg _) hR.le
      _ ≤ e := hRe
  have hradial : |D v 0 - 1| ≤ 2 * e := by
    calc
      _ = |(D v₀ 0 - 1) + D (v - v₀) 0| := by rw [map_sub]; congr 1; simp
      _ ≤ |D v₀ 0 - 1| + |D (v - v₀) 0| := abs_add_le _ _
      _ ≤ 2 * e := by linarith only [hrad, herror]
  have hdlo : 1 - 2 * e ≤ D v 0 := by linarith only [(abs_le.mp hradial).1]
  have hdpos : 0 < D v 0 := by linarith only [he4, hdlo]
  refine ⟨hdpos, ?_⟩
  intro i
  obtain ⟨hprod, hmpos, hmq, hm, _, hlog, hnear⟩ := hfac i
  have hui : 0 ≤ Y i.succ ∧ Y i.succ ≤ ε := by fin_cases i <;> assumption
  have hvi : |v i.succ| ≤ Real.sqrt (Y i.succ) := by fin_cases i <;> assumption
  let l := fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y v
  have hl : |l| ≤ L := by
    calc
      _ ≤ ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y‖ * ‖v‖ :=
        (fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y).le_opNorm v
      _ ≤ L * 1 := mul_le_mul hlog hvnorm (norm_nonneg _) hL.le
      _ = L := mul_one _
  have hsqrtm : Real.sqrt (compactCoreFactor Y i) ≤ s := Real.sqrt_le_sqrt hmq
  have hsqrtu : Real.sqrt (Y i.succ) * |l| ≤ e := by
    calc
      _ ≤ Real.sqrt ε * L := mul_le_mul (Real.sqrt_le_sqrt hui.2) hl (abs_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ e := by simpa only [mul_comm] using hLe
  have hcoeff : Real.sqrt (compactCoreFactor Y i) +
      Real.sqrt (compactCoreFactor Y i) * Real.sqrt (Y i.succ) * |l| ≤ s + e := by
    have H : Real.sqrt (compactCoreFactor Y i) * (Real.sqrt (Y i.succ) * |l|) ≤ 1 * e :=
      mul_le_mul (hsqrtm.trans hs1.le) hsqrtu (by positivity) zero_le_one
    nlinarith only [H, hsqrtm]
  have hgain : s + e ≤ (1 - e) * D v 0 := by
    have H := mul_le_mul_of_nonneg_left hdlo hσ.le
    nlinarith only [H, hse, sq_nonneg e]
  have hd := compactCoreFactor_transverse_differential i
    (hF.differentiableAt (by norm_num)) (hm.differentiableAt (by norm_num)) hmpos hnear v
  have H := wall_multiplier_cone_bound hui.1 hmpos (θ := 1) (by simpa using hvi) hd
  simp only [mul_one] at H
  calc
    |D v i.succ| ≤ Real.sqrt (Y i.succ * compactCoreFactor Y i) *
        (Real.sqrt (compactCoreFactor Y i) + Real.sqrt (compactCoreFactor Y i) * Real.sqrt (Y i.succ) * |l|) := H
    _ ≤ Real.sqrt (Y i.succ * compactCoreFactor Y i) * ((1 - e) * D v 0) :=
      mul_le_mul_of_nonneg_left (hcoeff.trans hgain) (Real.sqrt_nonneg _)
    _ = (1 - e) * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) * D v 0 := by rw [hprod]; ring
