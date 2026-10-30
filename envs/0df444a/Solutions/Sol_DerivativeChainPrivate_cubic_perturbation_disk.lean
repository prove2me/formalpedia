-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_perturbation_disk
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:04:46.700837+00:00
-- url     : https://prove2.me/submissions/e6d70e57-b3f0-47c5-9c8b-a80cfbc1de56

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (u v w o a : ℂ) (R t : ℝ) (ht : 0 ≤ t)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R) :
    ‖u+(t : ℂ)*a-o‖ ≤ R+t*‖a‖ ∧
      ‖v-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ ∧ ‖w-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ := by
  have hn : ‖(t : ℂ)*a‖ = t*‖a‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  have hpert (x : ℂ) (hx : ‖x-o‖ ≤ R) : ‖x-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ := by
    have heq : x-(t : ℂ)*a/2-o = (x-o)-(t : ℂ)*a/2 := by ring
    rw [heq]
    have h := norm_sub_le (x-o) ((t : ℂ)*a/2)
    rw [norm_div,hn] at h
    norm_num only [Complex.norm_ofNat] at h
    nlinarith only [h,hx,mul_nonneg ht (norm_nonneg a)]
  refine ⟨?_,hpert v hv,hpert w hw⟩
  have heq : u+(t : ℂ)*a-o = (u-o)+(t : ℂ)*a := by ring
  rw [heq]
  have h := norm_add_le (u-o) ((t : ℂ)*a)
  rw [hn] at h
  linarith only [h,hu]
