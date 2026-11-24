-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallA.discreteTopology_of_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:37.660338+00:00
-- url     : https://prove2.me/submissions/d1e901c1-8ecb-4f20-b521-bfa8db6ccc1f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul

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
theorem _root_.solution {Λ₁ Λ : Submodule ℤ E} [DiscreteTopology Λ₁] {N : ℤ}
    (hN : N ≠ 0) (h : ∀ y ∈ Λ, N • y ∈ Λ₁) : DiscreteTopology Λ := by
  refine DiscreteTopology.of_continuous_injective (β := Λ₁)
    (f := fun y : Λ ↦ (⟨N • (y : E), h y y.2⟩ : Λ₁)) ?_ ?_
  · exact ((continuous_zsmul N).comp continuous_subtype_val).subtype_mk _
  · intro y z hyz
    have h' : N • (y : E) = N • (z : E) := congrArg Subtype.val hyz
    rw [← Int.cast_smul_eq_zsmul ℝ N (y : E), ← Int.cast_smul_eq_zsmul ℝ N (z : E)] at h'
    exact Subtype.ext (smul_right_injective E (Int.cast_ne_zero.mpr hN) h')
end Formalism.HermitianLattices.Ext.L3.BallA
