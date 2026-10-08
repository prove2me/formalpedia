-- Prove2me | solution 1 for CoulombGauss.divergence_coulombKernel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:52:24.891984+00:00
-- url     : https://prove2.me/submissions/deb7a58d-5ca5-4019-aa18-3317b8657de1

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

set_option autoImplicit false

namespace CoulombGauss

lemma hasFDerivAt_normCube_8bfe (r r' : Vec3) :
    HasFDerivAt (fun x : Vec3 => ‖x - r'‖ ^ 3)
      (((3 * ‖r - r'‖ ^ ((3:ℝ) - 2)) • innerSL ℝ (r - r')).comp
        (ContinuousLinearMap.id ℝ Vec3)) r := by
  have h1 := hasFDerivAt_norm_rpow (r - r') (p := 3) (by norm_num)
  have h2 : HasFDerivAt (fun x : Vec3 => x - r') (ContinuousLinearMap.id ℝ Vec3) r :=
    (hasFDerivAt_id r).sub_const r'
  have h3 := h1.comp r h2
  have e : (fun x : Vec3 => ‖x - r'‖ ^ 3) =
      (fun x : Vec3 => ‖x‖ ^ (3:ℝ)) ∘ (fun x => x - r') := by
    funext x
    show ‖x - r'‖ ^ 3 = ‖x - r'‖ ^ ((3:ℕ):ℝ)
    rw [Real.rpow_natCast]
  rw [e]
  exact h3

lemma component_eq_8bfe (r' : Vec3) (i : Fin 3) :
    (fun x => coulombKernel x r' i) = fun x : Vec3 => (‖x - r'‖ ^ 3)⁻¹ * (x i - r' i) := by
  funext x
  simp [coulombKernel]

end CoulombGauss

open CoulombGauss in
theorem solution (r r' : Vec3) (h : r ≠ r') :
    DifferentiableAt ℝ (fun x => coulombKernel x r') r ∧
      divergence (fun x => coulombKernel x r') r = 0 := by
  have hy : r - r' ≠ 0 := sub_ne_zero.mpr h
  have hn : ‖r - r'‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hN3 : ‖r - r'‖ ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have hg := (hasFDerivAt_inv hN3).comp r (hasFDerivAt_normCube_8bfe r r')
  have hsub : HasFDerivAt (fun x : Vec3 => x - r') (ContinuousLinearMap.id ℝ Vec3) r :=
    (hasFDerivAt_id r).sub_const r'
  constructor
  · exact hg.differentiableAt.smul hsub.differentiableAt
  · unfold divergence
    have key : ∀ i : Fin 3,
        fderiv ℝ (fun x => coulombKernel x r' i) r (EuclideanSpace.single i 1)
          = (‖r - r'‖ ^ 3)⁻¹
            - 3 * ‖r - r'‖ * ((‖r - r'‖ ^ 3) ^ 2)⁻¹ * (r i - r' i) ^ 2 := by
      intro i
      have hc : HasFDerivAt (fun x : Vec3 => x i - r' i)
          (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ) r :=
        (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).hasFDerivAt.sub_const (r' i)
      have hm : HasFDerivAt (fun x : Vec3 => (‖x - r'‖ ^ 3)⁻¹ * (x i - r' i)) _ r :=
        hg.mul hc
      have h32 : ‖r - r'‖ ^ ((3:ℝ) - 2) = ‖r - r'‖ := by norm_num
      rw [component_eq_8bfe, hm.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
        innerSL_apply_apply, EuclideanSpace.inner_single_right,
        h32, PiLp.sub_apply, smul_eq_mul]
      simp
      ring
    simp only [key, Fin.sum_univ_three]
    have hs := EuclideanSpace.real_norm_sq_eq (r - r')
    rw [Fin.sum_univ_three] at hs
    simp only [PiLp.sub_apply] at hs
    have e2 : ∀ a b c n : ℝ, n ≠ 0 → n ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 →
        ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * a ^ 2)
          + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * b ^ 2)
          + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * c ^ 2) = 0 := by
      intro a b c n hn0 hsum
      have : a ^ 2 + b ^ 2 + c ^ 2 = n ^ 2 := hsum.symm
      have h' : ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * a ^ 2)
          + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * b ^ 2)
          + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * c ^ 2)
          = 3 * (n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
      rw [h', this]
      field_simp
      ring
    exact e2 _ _ _ _ hn hs
