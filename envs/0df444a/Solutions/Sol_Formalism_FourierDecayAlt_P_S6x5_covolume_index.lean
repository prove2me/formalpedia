-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.covolume_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:33.7032+00:00
-- url     : https://prove2.me/submissions/4402412b-fc83-435a-a686-b6d8d1c75e15

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

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
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ V)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂]
    (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ := by
  classical
  have : Module.Free ℤ L₁ := ZLattice.module_free ℝ L₁
  have : Module.Free ℤ L₂ := ZLattice.module_free ℝ L₂
  have : Module.Finite ℤ L₁ := ZLattice.module_finite ℝ L₁
  have : Module.Finite ℤ L₂ := ZLattice.module_finite ℝ L₂
  let b₂ := Free.chooseBasis ℤ L₂
  let b₁ := (Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq
    (β := Free.ChooseBasisIndex ℤ L₂)
    (by rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ, ZLattice.rank ℝ]))
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ (b₂.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ (b₂.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h2 : (b₂.ofZLatticeBasis ℝ).det ((↑) ∘ b₂) = 1 := by
    have : ((↑) ∘ b₂ : _ → V) = b₂.ofZLatticeBasis ℝ := by ext; simp
    rw [this, Basis.det_self]
  have hrel : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup =
      (b₂.det (fun i => (⟨b₁ i, h (SetLike.coe_mem _)⟩ : L₂))).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂
  rw [h2, abs_one, mul_one, hrel, Nat.cast_natAbs, Int.cast_abs]
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (SetLike.coe_mem _)⟩ i)
end Formalism.FourierDecayAlt.P.S6x5
