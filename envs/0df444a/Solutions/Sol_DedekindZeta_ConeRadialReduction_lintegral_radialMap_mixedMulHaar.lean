-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.lintegral_radialMap_mixedMulHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:34.041033+00:00
-- url     : https://prove2.me/submissions/555f6f59-8163-49a0-b449-5127d9c3c81d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x, h x ∂(DedekindZeta.mixedMulHaar K) := by
  set s : ℝ := t ^ ((finrank ℚ K : ℝ)⁻¹) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos ht _
  set c : mixedSpace K := s • (1 : mixedSpace K) with hc
  have hcN : mixedEmbedding.norm c ≠ 0 := by
    rw [hc, mixedEmbedding.norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hspos.ne')
  have hrw : (fun x : mixedSpace K => h (radialMap K t x))
      = fun x => h (x * c) := by
    funext x
    congr 1
    rw [radialMap, hc, mul_smul_comm, mul_one]
  rw [show (∫⁻ x, h (radialMap K t x) ∂(DedekindZeta.mixedMulHaar K))
        = ∫⁻ x, h (x * c) ∂(DedekindZeta.mixedMulHaar K) from by rw [hrw]]
  exact DedekindZeta.lintegral_comp_mul_right_mixedMulHaar K h hh hcN
end DedekindZeta.ConeRadialReduction
