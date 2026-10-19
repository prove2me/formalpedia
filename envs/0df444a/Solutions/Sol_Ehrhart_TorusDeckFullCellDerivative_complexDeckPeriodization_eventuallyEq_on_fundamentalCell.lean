-- Prove2me | solution 1 for Ehrhart.TorusDeckFullCellDerivative.complexDeckPeriodization_eventuallyEq_on_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/0af46f8f-25ef-446c-9eb7-1faeabe1e038

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckPeriodization_exists_finite_complexDeckPeriodization_support_near
import Theorems.Thm_Ehrhart_TorusDeckFundamentalCell_angularFundamentalBox_integer_shift_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckFullCellDerivative
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge TorusDeckPeriodization TorusDeckFundamentalCell
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
namespace Ehrhart.TorusDeckFullCellDerivative
theorem _root_.solution
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b)
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b) :
    complexDeckPeriodization ψ =ᶠ[
      𝓝 (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t)] ψ := by
  classical
  let z : TorusCharacters.LogSpace n :=
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint x t
  have hnot : ∀ q : Fin n → ℤ,
      q ≠ 0 →
        z + TorusCharacters.imaginaryShift q ∉ tsupport ψ := by
    intro q hq hzsupport
    have hinside := hcell hzsupport
    dsimp [z] at hinside
    rw [← logarithmicPoint_integer_add] at hinside
    have hshift :
        (fun i : Fin n => t i + (q i : ℝ)) ∈
          angularFundamentalBox b := by
      have hinner :
          (fun i : Fin n => t i + (q i : ℝ)) ∈
            angularFundamentalInterior b := by
        change
          ((logarithmicCoordinatesEquiv n).symm
            (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
              x (fun i : Fin n => t i + (q i : ℝ)))).2 ∈
              angularFundamentalInterior b at hinside
        simpa only [← logarithmicCoordinatesEquiv_apply,
          ContinuousLinearEquiv.symm_apply_apply] using hinside
      intro i
      exact ⟨(hinner i).1, (hinner i).2.le⟩
    exact hq (angularFundamentalBox_integer_shift_eq_zero ht hshift)
  have hvanish : ∀ q : Fin n → ℤ,
      q ≠ 0 →
        ∀ᶠ w : TorusCharacters.LogSpace n in 𝓝 z,
          ψ (w + TorusCharacters.imaginaryShift q) = 0 := by
    intro q hq
    have hzero := (notMem_tsupport_iff_eventuallyEq).mp (hnot q hq)
    have htranslate :
        Tendsto
          (fun w : TorusCharacters.LogSpace n =>
            w + TorusCharacters.imaginaryShift q)
          (𝓝 z)
          (𝓝 (z + TorusCharacters.imaginaryShift q)) :=
      (continuous_id.add continuous_const).continuousAt
    filter_upwards [htranslate hzero] with w hw
    simpa using hw
  obtain ⟨s, hs⟩ :=
    exists_finite_complexDeckPeriodization_support_near hψcompact z
  have hall :
      ∀ᶠ w : TorusCharacters.LogSpace n in 𝓝 z,
        ∀ q ∈ s, q ≠ 0 →
          ψ (w + TorusCharacters.imaginaryShift q) = 0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro q _
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall
        (fun _ hne => (hne hq).elim)
    · exact (hvanish q hq).mono (fun _ hw _ => hw)
  have hdeckzero :
      TorusCharacters.imaginaryShift
        (0 : Fin n → ℤ) = 0 := by
    ext i
    simp [TorusCharacters.imaginaryShift]
  change complexDeckPeriodization ψ =ᶠ[𝓝 z] ψ
  filter_upwards [hs, hall] with w hw hwall
  change
    (∑' q : Fin n → ℤ,
      ψ (w + TorusCharacters.imaginaryShift q)) = ψ w
  calc
    (∑' q : Fin n → ℤ,
      ψ (w + TorusCharacters.imaginaryShift q)) =
      ∑ q ∈ s,
        ψ (w + TorusCharacters.imaginaryShift q) :=
      tsum_eq_sum (fun q hq => hw q hq)
    _ = ψ (w + TorusCharacters.imaginaryShift
      (0 : Fin n → ℤ)) := by
      exact Finset.sum_eq_single (0 : Fin n → ℤ)
        (fun q hqs hq => hwall q hqs hq)
        (fun hzero => hw (0 : Fin n → ℤ) hzero)
    _ = ψ w := by
      rw [hdeckzero, add_zero]
end Ehrhart.TorusDeckFullCellDerivative
