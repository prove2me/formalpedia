-- Prove2me | solution 1 for Ehrhart.TorusDeckPeriodization.exists_finite_complexDeckPeriodization_support_near
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/7eaeee7b-37d1-44d3-adbb-39fb04bf6335

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_norm_imaginaryShift_coordinate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckPeriodization
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckPeriodization
theorem _root_.solution
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (x : TorusCharacters.LogSpace n) :
    ∃ s : Finset (Fin n → ℤ),
      ∀ᶠ y : TorusCharacters.LogSpace n in 𝓝 x,
        ∀ q : Fin n → ℤ,
          q ∉ s →
            ψ (y + TorusCharacters.imaginaryShift q) = 0 := by
  classical
  obtain ⟨R, hRpos, hR⟩ :=
    hψcompact.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((R + (‖x‖ + 1)) / (2 * Real.pi))
  let s : Finset (Fin n → ℤ) :=
    Fintype.piFinset
      (fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ))
  refine ⟨s, ?_⟩
  filter_upwards
    [Metric.ball_mem_nhds x (show 0 < (1 : ℝ) by norm_num)]
    with y hy
  intro q hq
  by_contra hnonzero
  have hsupport :
      y + TorusCharacters.imaginaryShift q ∈ tsupport ψ :=
    subset_closure ((mem_support).mpr hnonzero)
  have himage :
      ‖y + TorusCharacters.imaginaryShift q‖ ≤ R :=
    hR _ hsupport
  have hyx : ‖y - x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hybound : ‖y‖ ≤ ‖x‖ + 1 := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1 ; abel
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  have hdeck :
      ‖TorusCharacters.imaginaryShift q‖ ≤
        R + (‖x‖ + 1) := by
    calc
      ‖TorusCharacters.imaginaryShift q‖ =
          ‖(y + TorusCharacters.imaginaryShift q) - y‖ := by
            congr 1 ; abel
      _ ≤ ‖y + TorusCharacters.imaginaryShift q‖ + ‖y‖ :=
        norm_sub_le _ _
      _ ≤ R + (‖x‖ + 1) := add_le_add himage hybound
  have hpos : 0 < 2 * Real.pi := by positivity
  have hNmul :
      R + (‖x‖ + 1) < (N : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ hpos).mp hN
  have hmember : q ∈ s := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have hcoord :=
      (norm_le_pi_norm (TorusCharacters.imaginaryShift q) i).trans
        hdeck
    rw [norm_imaginaryShift_coordinate] at hcoord
    have habs : |(q i : ℝ)| < (N : ℝ) :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt hcoord hNmul) hpos.le
    have hleft : (-(N : ℤ)) ≤ q i := by
      exact_mod_cast (le_of_lt (abs_lt.mp habs).1)
    have hright : q i ≤ (N : ℤ) := by
      exact_mod_cast (le_of_lt (abs_lt.mp habs).2)
    exact Finset.mem_Icc.mpr ⟨hleft, hright⟩
  exact hq hmember
end Ehrhart.TorusDeckPeriodization
