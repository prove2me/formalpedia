-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:56:04.302466+00:00
-- url     : https://prove2.me/submissions/ec08e2d5-daf1-4df8-b546-d86dfb08c0c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (q s Δ : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hΔ : 0 ≤ Δ) :
    0 ≤ Real.exp (-(q*s)) ∧ Real.exp (-(q*s)) ≤ 1 ∧
    0 ≤ Real.exp (-(q*(s+Δ))) ∧
    Real.exp (-(q*(s+Δ))) ≤ 1 ∧
    |Real.exp (-(q*(s+Δ))) - Real.exp (-(q*s))| ≤ q*Δ := by
  have ha : 0 ≤ q*s := mul_nonneg hq hs
  have hb : 0 ≤ q*Δ := mul_nonneg hq hΔ
  have hab : 0 ≤ q*(s+Δ) :=
    mul_nonneg hq (add_nonneg hs hΔ)
  have hS : Real.exp (-(q*s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hT : Real.exp (-(q*(s+Δ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hab)
  have hST : Real.exp (-(q*(s+Δ))) ≤ Real.exp (-(q*s)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hE : Real.exp (-(q*(s+Δ))) =
      Real.exp (-(q*s)) * Real.exp (-(q*Δ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hSmall : 0 ≤ 1 - Real.exp (-(q*Δ)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hb))
  have hLinear : 1 - Real.exp (-(q*Δ)) ≤ q*Δ := by
    have h := Real.add_one_le_exp (-(q*Δ))
    linarith
  have hBound : Real.exp (-(q*s)) - Real.exp (-(q*(s+Δ))) ≤ q*Δ := by
    calc
      _ = Real.exp (-(q*s)) * (1 - Real.exp (-(q*Δ))) := by
        rw [hE]
        ring
      _ ≤ 1 * (1 - Real.exp (-(q*Δ))) :=
        mul_le_mul_of_nonneg_right hS hSmall
      _ = 1 - Real.exp (-(q*Δ)) := one_mul _
      _ ≤ q*Δ := hLinear
  refine ⟨Real.exp_nonneg _,hS,Real.exp_nonneg _,hT,?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hST)]
  linarith
