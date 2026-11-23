-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.finsum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:59.848856+00:00
-- url     : https://prove2.me/submissions/de8bf491-d863-4730-ac0e-9f1318b2ef43

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {X Y T : Type} [AddGroup Y] [Fintype T] (κ : X → Y)
    (hκ : Function.Bijective κ) (g : T → Y) (f : T → ℂ) [∀ τ x, Decidable (g τ = -κ x)] :
    (Function.support fun x => ∑ τ : T, if g τ = -κ x then f τ else 0).Finite ∧
      ∑ᶠ x, ∑ τ : T, (if g τ = -κ x then f τ else 0) = ∑ τ : T, f τ := by
  have hfin : ∀ τ : T, (Function.support fun x => if g τ = -κ x then f τ else 0).Finite := by
    intro τ
    apply Set.Subsingleton.finite
    intro x hx y hy
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx hy
    apply hκ.1
    rw [← neg_inj, ← hx.1, ← hy.1]
  refine ⟨?_, ?_⟩
  · refine (Set.finite_iUnion hfin).subset ?_
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    by_contra hcon
    apply hx
    apply Finset.sum_eq_zero
    intro τ _
    by_contra h0
    exact hcon (Set.mem_iUnion.mpr ⟨τ, h0⟩)
  · rw [finsum_sum_comm _ _ (fun τ _ => hfin τ)]
    apply Finset.sum_congr rfl
    intro τ _
    obtain ⟨x0, hx0⟩ := hκ.2 (-g τ)
    rw [finsum_eq_single _ x0]
    · rw [if_pos (by rw [hx0, neg_neg])]
    · intro x hx
      rw [if_neg]
      intro h
      apply hx
      apply hκ.1
      rw [hx0, h, neg_neg]
end Formalism.FourierDecayAlt.P.A5x6
