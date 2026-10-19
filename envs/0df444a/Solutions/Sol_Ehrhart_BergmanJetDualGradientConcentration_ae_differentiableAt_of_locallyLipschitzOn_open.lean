-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_of_locallyLipschitzOn_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8f2f963c-a3d3-4a78-a029-828fcf8daba1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDualGradientConcentration
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDualGradientConcentration
theorem _root_.solution
    {n : ℕ} {s : Set (Space n)}
    (hs : IsOpen s) {f : Space n → ℝ}
    (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x : Space n ∂(volume : Measure (Space n)),
      x ∈ s → DifferentiableAt ℝ f x := by
  classical
  have hlocal : ∀ x : s,
      ∃ (u : Set (Space n)) (C : ℝ≥0),
        IsOpen u ∧ (x : Space n) ∈ u ∧
          u ⊆ s ∧ LipschitzOnWith C f u := by
    intro x
    obtain ⟨C, t, ht, hft⟩ := hf x.property
    have ht' : t ∈ 𝓝 (x : Space n) := by
      rw [nhdsWithin_eq_nhds.mpr (hs.mem_nhds x.property)] at ht
      exact ht
    obtain ⟨v, hvt, hvopen, hxv⟩ := mem_nhds_iff.mp ht'
    refine ⟨v ∩ s, C, hvopen.inter hs,
      ⟨hxv, x.property⟩, inter_subset_right, ?_⟩
    exact hft.mono (fun y hy => hvt hy.1)
  choose u C huopen hux hus hflip using hlocal
  obtain ⟨T, hT, hTu⟩ :=
    TopologicalSpace.isOpen_iUnion_countable u huopen
  have hucover : (⋃ x : s, u x) = s := by
    apply le_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hus i hi
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hux ⟨x, hx⟩⟩
  have hTcover : (⋃ i ∈ T, u i) = s := hTu.trans hucover
  have hae :
      ∀ᵐ x : Space n
        ∂((volume : Measure (Space n)).restrict s),
        DifferentiableAt ℝ f x := by
    rw [← hTcover]
    apply (ae_restrict_biUnion_iff u hT _).2
    intro i _hi
    have hrad :
        ∀ᵐ x : Space n
          ∂((volume : Measure (Space n)).restrict (u i)),
          DifferentiableWithinAt ℝ f (u i) x :=
      (hflip i).ae_differentiableWithinAt (huopen i).measurableSet
    filter_upwards [hrad,
      ae_restrict_mem (huopen i).measurableSet] with x hx hxu
    exact hx.differentiableAt ((huopen i).mem_nhds hxu)
  exact ae_imp_of_ae_restrict hae
end Ehrhart.BergmanJetDualGradientConcentration
