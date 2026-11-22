-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_scale_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T11:41:22.617999+00:00
-- url     : https://prove2.me/submissions/33e82ae6-ceb1-414b-872c-fb8ef19579ac

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set

theorem solution (W : ℝ → ℝ) (a β0 β K : ℝ) (ha : 0 < a) (hβ : β0 ≤ β)
    (hWnn : ∀ x : ℝ, 0 < x → 0 ≤ W x)
    (hint0 : IntegrableOn (fun x : ℝ => Real.exp (-(β0 * x)) * W x) (Ioi (0 : ℝ)))
    (hint1 : IntegrableOn (fun x : ℝ => Real.exp (-(β * x)) * W x) (Ioi a))
    (hK : (∫ x in Ioi (0 : ℝ), Real.exp (-(β0 * x)) * W x) ≤ K) :
    (∫ x in Ioi a, Real.exp (-(β * x)) * W x) ≤ Real.exp (-(β - β0) * a) * K := by
  let C := Real.exp (-(β - β0) * a)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hbase (x : ℝ) (hx : 0 < x) : 0 ≤ Real.exp (-(β0 * x)) * W x :=
    mul_nonneg (Real.exp_pos _).le (hWnn x hx)
  have hsubset : Ioi a ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ha.le
  have hdom (x : ℝ) (hx : x ∈ Ioi a) :
      Real.exp (-(β * x)) * W x ≤ C * (Real.exp (-(β0 * x)) * W x) := by
    have hshift : Real.exp (-(β - β0) * x) ≤ C :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (le_of_lt hx) (neg_nonpos.mpr (sub_nonneg.mpr hβ)))
    have hsplit : -(β * x) = -(β - β0) * x + -(β0 * x) := by ring
    rw [hsplit, Real.exp_add, mul_assoc]
    exact mul_le_mul_of_nonneg_right hshift (hbase x (hsubset hx))
  have hAE : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun x => Real.exp (-(β0 * x)) * W x) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbase)
  calc
    (∫ x in Ioi a, Real.exp (-(β * x)) * W x)
        ≤ ∫ x in Ioi a, C * (Real.exp (-(β0 * x)) * W x) :=
      setIntegral_mono_on hint1 ((hint0.mono_set hsubset).const_mul C) measurableSet_Ioi hdom
    _ = C * (∫ x in Ioi a, Real.exp (-(β0 * x)) * W x) := integral_const_mul C _
    _ ≤ C * (∫ x in Ioi (0 : ℝ), Real.exp (-(β0 * x)) * W x) :=
      mul_le_mul_of_nonneg_left (setIntegral_mono_set hint0 hAE (Eventually.of_forall hsubset)) hC
    _ ≤ C * K := mul_le_mul_of_nonneg_left hK hC
