-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularBoxIntegral_eq_of_coordinate_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/cdc6479e-817a-4bbe-939d-a2a20892a9c4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_continuous_integrable_angularBox

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution
    {n : ℕ} {g h : Space (n + 1) → ℂ}
    (hg : Continuous g) (hh : Continuous h)
    (i : Fin (n + 1))
    (hslice : ∀ y : Fin n → ℝ,
      (∫ t : ℝ in 0..1, g (i.insertNth t y)) =
        ∫ t : ℝ in 0..1, h (i.insertNth t y)) :
    (∫ t : Space (n + 1),
      g t ∂(angularBoxMeasure (n + 1))) =
      ∫ t : Space (n + 1),
        h t ∂(angularBoxMeasure (n + 1)) := by
  let μ : Fin (n + 1) → Measure ℝ :=
    fun _ => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let ν : Measure (Fin n → ℝ) :=
    Measure.pi fun j : Fin n => μ (i.succAbove j)
  let e :
      (ℝ × (Fin n → ℝ)) ≃ᵐ Space (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i).symm
  have he :
      MeasurePreserving e ((μ i).prod ν)
        (angularBoxMeasure (n + 1)) := by
    simpa [angularBoxMeasure, μ, ν, e] using
      (MeasureTheory.measurePreserving_piFinSuccAbove μ i).symm
  have hgi :
      Integrable
        (fun z : ℝ × (Fin n → ℝ) =>
          g (i.insertNth z.1 z.2))
        ((μ i).prod ν) := by
    have h' := he.integrable_comp_of_integrable
      (continuous_integrable_angularBox hg)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h'
  have hhi :
      Integrable
        (fun z : ℝ × (Fin n → ℝ) =>
          h (i.insertNth z.1 z.2))
        ((μ i).prod ν) := by
    have h' := he.integrable_comp_of_integrable
      (continuous_integrable_angularBox hh)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h'
  calc
    (∫ t : Space (n + 1),
      g t ∂(angularBoxMeasure (n + 1))) =
      ∫ z : ℝ × (Fin n → ℝ),
        g (i.insertNth z.1 z.2) ∂((μ i).prod ν) := by
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using (he.integral_comp' g).symm
    _ = ∫ y : Fin n → ℝ,
          (∫ t : ℝ, g (i.insertNth t y) ∂(μ i)) ∂ν :=
        MeasureTheory.integral_prod_symm _ hgi
    _ = ∫ y : Fin n → ℝ,
          (∫ t : ℝ, h (i.insertNth t y) ∂(μ i)) ∂ν := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          change
            (∫ t : ℝ in Set.Ioc (0 : ℝ) 1,
              g (i.insertNth t y)) =
              ∫ t : ℝ in Set.Ioc (0 : ℝ) 1,
                h (i.insertNth t y)
          simpa only [← intervalIntegral.integral_of_le
            (by norm_num : (0 : ℝ) ≤ 1)] using hslice y
    _ = ∫ z : ℝ × (Fin n → ℝ),
          h (i.insertNth z.1 z.2) ∂((μ i).prod ν) :=
        (MeasureTheory.integral_prod_symm _ hhi).symm
    _ = ∫ t : Space (n + 1),
          h t ∂(angularBoxMeasure (n + 1)) := by
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using (he.integral_comp' h)
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
