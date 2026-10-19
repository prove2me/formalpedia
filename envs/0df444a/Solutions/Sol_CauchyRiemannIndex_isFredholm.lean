-- Prove2me | solution 1 for CauchyRiemannIndex.isFredholm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T10:26:15.377864+00:00
-- url     : https://prove2.me/submissions/d7717706-ed67-46e0-9584-8097f30f0168

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.ConjExponents
import Theorems.Thm_CauchyRiemannIndex_semiFredholm
import Theorems.Thm_CauchyRiemannIndex_cokernel_eq_kernel_adjoint

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus) :
    IsFredholmCR p S := by
  have hsf := semiFredholm n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hH : p.HolderConjugate p.conjExponent := inferInstance
  have hpq : 1 / p + 1 / p.conjExponent = 1 := by
    simpa [one_div] using hH.inv_add_inv_eq_one
  have hck := cokernel_eq_kernel_adjoint n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus
    p.conjExponent hpq
  exact ⟨hsf.1, hsf.2, hck.1⟩
