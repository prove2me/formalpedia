-- Prove2me | solution 1 for Ehrhart.GenuineJetAdaptedBasisCounting.card_adaptedIndices_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/a7bb7f3f-02be-438a-b231-0bd1e8615627

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_GenuineJetAdaptedBasisCounting_span_adaptedIndices_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.GenuineJetAdaptedBasisCounting
open Set Module
open scoped BigOperators InnerProductSpace
namespace Ehrhart.GenuineJetAdaptedBasisCounting
theorem _root_.solution {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V)
    (hb : ∀ i, b i ∈ S ∨ b i ∈ Sᗮ) :
    (adaptedIndices b S).card = Module.finrank ℂ S := by
  classical
  have hindependent :
      LinearIndependent ℂ
        (fun i : adaptedIndices b S => b (i : ι)) := by
    exact b.orthonormal.linearIndependent.comp
      (fun i : adaptedIndices b S => (i : ι)) Subtype.val_injective
  have hcard := finrank_span_eq_card hindependent
  rw [span_adaptedIndices_eq b S hb] at hcard
  simpa using hcard.symm
end Ehrhart.GenuineJetAdaptedBasisCounting
