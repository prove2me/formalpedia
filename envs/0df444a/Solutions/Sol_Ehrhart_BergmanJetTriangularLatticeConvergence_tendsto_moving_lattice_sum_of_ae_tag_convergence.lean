-- Prove2me | solution 1 for Ehrhart.BergmanJetTriangularLatticeConvergence.tendsto_moving_lattice_sum_of_ae_tag_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/12e48947-0066-4b2a-b189-55488134efd5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_triangularUnitLatticeStep_integrable
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_integral_triangularUnitLatticeStep_eq_lattice_sum
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_triangularUnitLatticeStep_eq_tag_of_mem
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_triangularUnitLatticeStep_eq_zero_of_not_mem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTriangularLatticeConvergence
theorem _root_.solution {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (hs : s ⊆ (B : Set (Space n)))
    (hsm : MeasurableSet s)
    (G : ℕ → Space n → ℝ)
    (g : Space n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, 0 < k → ∀ u ∈ s,
      u ∈ scaledIntegerLattice n k → ‖G k u‖ ≤ C)
    (hpoint : ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      Tendsto (fun k : ℕ =>
        s.indicator (G (k + 1))
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop (𝓝 (s.indicator g x))) :
    Tendsto
      (fun k : ℕ =>
        (∑' u : ↑(s ∩ scaledIntegerLattice n (k + 1)),
          G (k + 1) u) / ((k + 1 : ℕ) : ℝ) ^ n)
      atTop (𝓝 (∫ x in s, g x
        ∂(volume : Measure (Space n)))) := by
  classical
  have hmajor : Integrable
      ((B : Set (Space n)).indicator
        (fun _ : Space n => C))
      (volume : Measure (Space n)) :=
    (integrableOn_const
      (μ := (volume : Measure (Space n)))
      (C := C)
      (BoxIntegral.Box.measure_coe_lt_top B
        (volume : Measure (Space n))).ne).integrable_indicator
      B.measurableSet_coe
  have hsteps : ∀ k : ℕ, AEStronglyMeasurable
      (triangularUnitLatticeStep B s G k)
      (volume : Measure (Space n)) :=
    fun k => (triangularUnitLatticeStep_integrable B s G k).1
  have hdom : ∀ k : ℕ, ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      ‖triangularUnitLatticeStep B s G k x‖ ≤
        (B : Set (Space n)).indicator
          (fun _ : Space n => C) x := by
    intro k
    filter_upwards [] with x
    by_cases hx : x ∈ (B : Set (Space n))
    · rw [triangularUnitLatticeStep_eq_tag_of_mem B hB s G k x hx]
      rw [Set.indicator_of_mem hx]
      let u : Space n :=
        BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) x)
      have hulattice : u ∈ scaledIntegerLattice n (k + 1) := by
        change
          BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) x) ∈
            scaledIntegerLattice n (k + 1)
        rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
        exact BoxIntegral.unitPartition.tag_mem_smul_span
          (k + 1) (BoxIntegral.unitPartition.index (k + 1) x)
      by_cases hu : u ∈ s
      · simpa [u, Set.indicator_of_mem hu] using
          hbound (k + 1) (Nat.zero_lt_succ k) u hu hulattice
      · rw [Set.indicator_of_notMem hu]
        simpa using hC
    · rw [triangularUnitLatticeStep_eq_zero_of_not_mem B s G k x hx]
      rw [Set.indicator_of_notMem hx]
      simp
  have hlim : ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      Tendsto (fun k : ℕ => triangularUnitLatticeStep B s G k x)
        atTop (𝓝 (s.indicator g x)) := by
    filter_upwards [hpoint] with x hxpoint
    by_cases hx : x ∈ (B : Set (Space n))
    · exact hxpoint.congr' (Filter.Eventually.of_forall fun k =>
        (triangularUnitLatticeStep_eq_tag_of_mem B hB s G k x hx).symm)
    · have hxs : x ∉ s := fun h => hx (hs h)
      have hzero : s.indicator g x = 0 := Set.indicator_of_notMem hxs g
      rw [hzero]
      exact (tendsto_congr'
        (Filter.Eventually.of_forall fun k =>
          triangularUnitLatticeStep_eq_zero_of_not_mem B s G k x hx)).2
        tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    ((B : Set (Space n)).indicator
      (fun _ : Space n => C))
    hsteps hmajor hdom hlim
  simpa [integral_triangularUnitLatticeStep_eq_lattice_sum B hB s hs G,
    MeasureTheory.integral_indicator hsm] using hdct
end Ehrhart.BergmanJetTriangularLatticeConvergence
