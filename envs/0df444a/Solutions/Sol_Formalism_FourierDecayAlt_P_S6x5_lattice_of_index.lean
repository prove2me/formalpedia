-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.lattice_of_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:45.046398+00:00
-- url     : https://prove2.me/submissions/e7067617-4b2f-4527-aa76-7cc24a72cb7e

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_covolume_index
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_scalInv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_map_scal_eq_comap
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_covolume_scal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Module MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (M₁ M₂ : Submodule ℤ V)
    [DiscreteTopology M₁] [IsZLattice ℝ M₁] (h : M₁ ≤ M₂)
    (hn : M₁.toAddSubgroup.relIndex M₂.toAddSubgroup ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    DiscreteTopology (M₂.map (scal V c)) ∧
    Submodule.span ℝ (M₂.map (scal V c) : Set V) = ⊤ ∧
    ZLattice.covolume (M₂.map (scal V c)) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume M₁ μ /
        (M₁.toAddSubgroup.relIndex M₂.toAddSubgroup : ℝ) := by
  set n := M₁.toAddSubgroup.relIndex M₂.toAddSubgroup with hn'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn

  have hsub : M₂ ≤ ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap := by
    intro x hx
    show (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)) x ∈ M₁
    rw [scalInv_apply, inv_inv, Nat.cast_smul_eq_nsmul]
    have := AddSubgroup.nsmul_index_mem (M₁.toAddSubgroup.addSubgroupOf M₂.toAddSubgroup) ⟨x, hx⟩
    exact this
  have hd : DiscreteTopology M₂ := DiscreteTopology.of_subset (t := (M₂ : Set V))
    (s := (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap : Set V))
    (inferInstanceAs (DiscreteTopology
      (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap))) hsub
  have hz : IsZLattice ℝ M₂ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := M₁)]
    exact Submodule.span_mono h⟩
  rw [map_scal_eq_comap c hc]
  refine ⟨inferInstance, IsZLattice.span_top, ?_⟩
  rw [covolume_scal μ M₂ c hc, covolume_index μ M₁ M₂ h, ← hn']
  field_simp
end Formalism.FourierDecayAlt.P.S6x5
