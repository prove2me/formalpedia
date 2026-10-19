-- Prove2me | solution 1 for Ehrhart.TorusDeckPeriodization.contDiff_complexDeckPeriodization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/8e393572-f326-4615-a25e-7ba1c90a1183

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_exists_finite_complexDeckPeriodization_support_near

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
    {n : ℕ} {r : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ r ψ)
    (hψcompact : HasCompactSupport ψ) :
    ContDiff ℝ r (complexDeckPeriodization ψ) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨s, hs⟩ :=
    exists_finite_complexDeckPeriodization_support_near hψcompact x
  let F : TorusCharacters.LogSpace n → ℂ :=
    fun y => ∑ q ∈ s,
      ψ (y + TorusCharacters.imaginaryShift q)
  have hF : ContDiff ℝ r F := by
    dsimp [F]
    apply ContDiff.sum
    intro q hq
    exact hψ.comp (contDiff_id.add contDiff_const)
  apply hF.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  change
    (∑' q : Fin n → ℤ,
      ψ (y + TorusCharacters.imaginaryShift q)) =
      ∑ q ∈ s, ψ (y + TorusCharacters.imaginaryShift q)
  exact tsum_eq_sum (fun q hq => hy q hq)
end Ehrhart.TorusDeckPeriodization
