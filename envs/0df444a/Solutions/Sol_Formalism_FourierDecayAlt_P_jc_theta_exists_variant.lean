-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jc_theta_exists_variant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:28.640222+00:00
-- url     : https://prove2.me/submissions/34049265-f4c7-4a1d-b8c2-e4d70734a0e0

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1
open NumberField
end Formalism.FourierDecayAlt.P.JCx1
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
private theorem setOf_threshold_values_finite (N : ℕ) (a : ℝ) (b d : ℕ → ℝ) (c : ℕ → ℕ → ℝ) :
    {x : ℝ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧ ((i = 1 ∧ x = a) ∨ (2 ≤ i ∧ x = b i) ∨
      (∃ s : ℕ, 2 ≤ s ∧ s + i ≤ N + 1 ∧ x = c i s) ∨ x = d i)}.Finite := by
  apply Set.Finite.subset (((Set.finite_Iic N).image b).union
    ((((Set.finite_Iic N).prod (Set.finite_Iic (N + 1))).image (fun q : ℕ × ℕ => c q.1 q.2)).union
      ((Set.finite_Iic N).image d)) |>.insert a)
  rintro x ⟨i, hi1, hiN, h | h | ⟨s, hs2, hsi, h⟩ | h⟩
  · rw [h.2]
    exact Set.mem_insert _ _
  · rw [h.2]
    exact Set.mem_insert_of_mem _ (Set.mem_union_left _ (Set.mem_image_of_mem b (Set.mem_Iic.2 hiN)))
  · rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (Set.mem_union_left _
      (Set.mem_image_of_mem (fun q : ℕ × ℕ => c q.1 q.2)
        (Set.mk_mem_prod (Set.mem_Iic.2 hiN) (Set.mem_Iic.2 (by omega))))))
  · rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (Set.mem_union_right _
      (Set.mem_image_of_mem d (Set.mem_Iic.2 hiN))))
end Formalism.FourierDecayAlt.P
section cutf
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.JCx1
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.JCx1
namespace Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end cutf
section lemE
open Formalism.FourierDecayAlt Filter Topology
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end lemE
section decayPart
open Finset Formalism.FourierDecayAlt
noncomputable section decayNC
namespace Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
end Formalism.FourierDecayAlt.P.JCx1.decay
end decayNC
end decayPart
section needsPart
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
namespace Formalism.FourierDecayAlt.P.JCx1.needs
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
section meas
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E} {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
end meas
end
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end needsPart
end

set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.ThetaExistence₂ := by
  intro ι _ G C de de' T T' l hf hpos
  have hfin : (G.thrSet C de de' T T' l).Finite := setOf_threshold_values_finite _ _ _ _ _
  have hne : (G.thrSet C de de' T T' l).Nonempty := by
    unfold Set.Nonempty Sz.Glob.thrSet
    simp only [Set.mem_setOf_eq]
    exact ⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩
  have hmem := hne.csSup_mem hfin
  have hgr : IsGreatest (G.thrSet C de de' T T' l) (sSup (G.thrSet C de de' T T' l)) :=
    ⟨hmem, fun x hx => le_csSup hfin.bddAbove hx⟩
  have hm0 : 0 < sSup (G.thrSet C de de' T T' l) := hpos _ hmem
  have hf0 : (G.f : ℝ) ≠ 0 := by exact_mod_cast (by omega : G.f ≠ 0)
  refine ⟨sSup (G.thrSet C de de' T T' l) ^ (-(1 / (G.f : ℝ))), Real.rpow_pos_of_pos hm0 _, ?_⟩
  have e : ((sSup (G.thrSet C de de' T T' l) ^ (-(1 / (G.f : ℝ)))) ^ G.f)⁻¹ = sSup (G.thrSet C de de' T T' l) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, neg_mul, one_div_mul_cancel hf0, Real.rpow_neg_one, inv_inv]
  rw [e]
  exact hgr
end Formalism.FourierDecayAlt.P
