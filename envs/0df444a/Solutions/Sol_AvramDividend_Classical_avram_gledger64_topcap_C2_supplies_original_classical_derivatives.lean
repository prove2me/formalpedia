-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger64_topcap_C2_supplies_original_classical_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:46:41.483284+00:00
-- url     : https://prove2.me/submissions/80dfac2b-00b6-46bb-afca-8017015be67d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped ENNReal Topology
noncomputable section

/-- The original top-cap C2 hypothesis supplies both pointwise classical
    derivative witnesses on the strictly positive reserve domain. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by
  have hcd : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) := by
    have hset : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} =
        Ioi (0 : ℝ) := by
      ext y
      simp [hTopCap]
    simpa only [hset] using hw_smooth
  have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hdiff : DifferentiableOn ℝ w (Ioi (0 : ℝ)) :=
    hcd.differentiableOn (by norm_num)
  have hderiv : ContDiffOn ℝ 1 (deriv w) (Ioi (0 : ℝ)) :=
    hcd.deriv_of_isOpen hopen (by norm_num)
  have hdiff2 : DifferentiableOn ℝ (deriv w) (Ioi (0 : ℝ)) :=
    hderiv.differentiableOn (by norm_num)
  intro y hy
  have hny : Ioi (0 : ℝ) ∈ 𝓝 y := hopen.mem_nhds hy
  refine ⟨((hdiff y hy).differentiableAt hny).hasDerivAt, ?_⟩
  have h : HasDerivAt (deriv w) (deriv (deriv w) y) y :=
    ((hdiff2 y hy).differentiableAt hny).hasDerivAt
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
