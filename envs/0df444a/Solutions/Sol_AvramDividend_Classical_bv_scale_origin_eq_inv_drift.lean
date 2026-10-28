-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_origin_eq_inv_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:57:32.600954+00:00
-- url     : https://prove2.me/submissions/665ddae6-dd6e-4fff-a906-98420198f78a

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_scale_pointwise
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_positive_convolution_powers_no_atom
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_exact_atom_from_atomless_powers
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The canonical geometric renewal atom and right continuity fix the BV scale origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    W 0 = 1 / X.drift := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hBV
  obtain ⟨κ, m, β, hκdef, hκac, hm0, hmsucc, hmsf, hβ,
    _, _, hβneg, _, hβfin, hβscale⟩ :=
    bv_esscher_canonical_geometric_scale_pointwise
      X hX q hq W hW hBV φ hφ hroot
  haveI : SFinite κ := by
    rw [hκdef]
    infer_instance
  have hpowers : ∀ n : ℕ, 0 < n →
      m n ({(0 : ℝ)} : Set ℝ) = 0 :=
    geometric_renewal_positive_convolution_powers_no_atom
      κ m hmsf hκac hmsucc
  have hatom : β ({(0 : ℝ)} : Set ℝ) =
      (ENNReal.ofReal X.drift)⁻¹ := by
    rw [hβ]
    exact geometric_renewal_exact_atom_from_atomless_powers
      m ((ENNReal.ofReal X.drift)⁻¹) (0 : ℝ) hm0 hpowers
  have hcut : β (Iic (0 : ℝ)) = β ({(0 : ℝ)} : Set ℝ) := by
    have hs : Iic (0 : ℝ) = Iio 0 ∪ {(0 : ℝ)} := by
      ext y
      simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
      exact le_iff_lt_or_eq
    rw [hs, measure_union]
    · simp [hβneg]
    · exact disjoint_left.mpr (by
        intro y hy hy0
        exact (mem_Iio.mp hy).ne hy0)
    · exact measurableSet_singleton _
  have hWcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0 :=
    (hW.2.2.1.continuousWithinAt (by simp)).mono
      (by intro x hx; exact le_of_lt (mem_Ioi.mp hx))
  have hExp : Continuous (fun x : ℝ => Real.exp (-(φ * x))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hLeft : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (W 0)) := by
    have ht := (hExp.continuousWithinAt.mul hWcont).tendsto
    change Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Real.exp (-(φ * (0 : ℝ))) * W 0)) at ht
    simpa using ht
  have hRight : Tendsto (fun x : ℝ => (β (Iic x)).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((β (Iic (0 : ℝ))).toReal)) :=
    (rightContinuous_cumulative_toReal_of_finite β hβfin 0).mono
      (by intro x hx; exact le_of_lt (mem_Ioi.mp hx))
  have heq : (fun x : ℝ => Real.exp (-(φ * x)) * W x) =ᶠ[
      nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => (β (Iic x)).toReal) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hβscale x (mem_Ioi.mp hx)
  have hlimit : W 0 = (β (Iic (0 : ℝ))).toReal :=
    tendsto_nhds_unique hLeft (hRight.congr' heq.symm)
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  calc
    W 0 = (β (Iic (0 : ℝ))).toReal := hlimit
    _ = ((ENNReal.ofReal X.drift)⁻¹).toReal := by rw [hcut, hatom]
    _ = 1 / X.drift := by
      rw [← ENNReal.ofReal_inv_of_pos hd]
      rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hd))]
      simp [one_div]
