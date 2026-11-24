-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallA.tendsto_card_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:39.624888+00:00
-- url     : https://prove2.me/submissions/aca24cf0-98b4-4a51-8d58-c92809c0b216

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_tendsto_card_div_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_covolume_div_covolume
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallA_discreteTopology_of_zsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module ZSpan Filter Topology Pointwise Bornology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallA
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ : Measure E) [μ.IsAddHaarMeasure]
namespace Formalism.HermitianLattices.Ext.L3.BallA
theorem _root_.solution (Λ₁ Λ : Submodule ℤ E) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    (hle : Λ₁ ≤ Λ) {N : ℤ} (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) {s : Set E}
    (hs₁ : IsBounded s) (hs₂ : MeasurableSet s) (hs₃ : Convex ℝ s) :
    Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 0 ∧
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • Λ : Set E) : ℝ) / n ^ finrank ℝ E)
      atTop (𝓝 (μ.real s * (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) /
        ZLattice.covolume Λ₁ μ)) := by
  have : DiscreteTopology Λ := discreteTopology_of_zsmul hN h
  have : IsZLattice ℝ Λ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := Λ₁)]
    exact Submodule.span_mono hle⟩
  have hidx := covolume_div_covolume μ Λ₁ Λ hle
  have h₁ := (ZLattice.covolume_pos Λ₁ μ).ne'
  have h₂ := (ZLattice.covolume_pos Λ μ).ne'
  have hne : (Λ₁.toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) ≠ 0 := by
    rw [← hidx]
    exact div_ne_zero h₁ h₂
  refine ⟨by exact_mod_cast hne, ?_⟩
  have key := tendsto_card_div_pow Λ μ hs₁ hs₂ (hs₃.addHaar_frontier μ)
  convert key using 2
  rw [← hidx]
  field_simp
end Formalism.HermitianLattices.Ext.L3.BallA
