-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.identity_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:29.058695+00:00
-- url     : https://prove2.me/submissions/aa58fec1-5718-4308-a108-ce280f19f401

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IdentityOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]
end Formalism.FourierDecayAlt.P
