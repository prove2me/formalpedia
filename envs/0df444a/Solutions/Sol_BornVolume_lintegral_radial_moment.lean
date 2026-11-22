-- Prove2me | solution 1 for BornVolume.lintegral_radial_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:59.662034+00:00
-- url     : https://prove2.me/submissions/059a95ee-9084-4baf-a699-b03a9198a2c5

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
namespace BornVolume
theorem _root_.solution (n : ℕ) :
    ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal (S ^ n * Real.exp (-S / 2))
      = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (n.factorial : ℝ)) := by
  have hnonneg : ∀ S ∈ Ioi (0 : ℝ), 0 ≤ S ^ n * Real.exp (-S / 2) := by
    intro S hS; simp only [mem_Ioi] at hS; positivity
  -- Bochner value: ∫ Sⁿ e^{−S/2} = 2^{n+1}·n!.
  have hbase : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-t / 2)
      = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1 / 2)
      (by positivity) (by norm_num)
    -- RHS: (1/(1/2))^(n+1) · Γ(n+1) = 2^{n+1}·n!.
    have hRHS : ((1 : ℝ) / (1 / 2)) ^ ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1)
        = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
      rw [Real.Gamma_nat_eq_factorial,
        show ((1 : ℝ) / (1 / 2)) = 2 by norm_num,
        show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hRHS] at h
    rw [← h]
    -- Match integrands: t^((n+1)-1) = tⁿ, exp(-(1/2·t)) = exp(-t/2) on Ioi 0.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show t ^ n * Real.exp (-t / 2) = t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(1 / 2 * t))
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast,
      show -(1 / 2 * t) = -t / 2 by ring]
  -- Integrability of `tⁿ·e^{−t/2}` on `Ioi 0`.
  have hint : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := 1 / 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos (by norm_num)
    apply h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show t ^ (n : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)) = t ^ n * Real.exp (-t / 2)
    rw [Real.rpow_natCast, Real.rpow_one, show -(1 / 2) * t = -t / 2 by ring]
  -- Bridge `ofReal ∘ Bochner = lintegral ∘ ofReal`.
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnonneg)),
    hbase]
end BornVolume
