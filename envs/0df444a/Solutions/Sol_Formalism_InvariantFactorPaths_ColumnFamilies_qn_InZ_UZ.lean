-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_InZ_UZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:53:23.998328+00:00
-- url     : https://prove2.me/submissions/f8eaaf8c-3999-4d88-b1b8-c8166bfdbbea

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowDiv_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_binomE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_divPowE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (u : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))
    (hu : u ∈ UZmon (glOps ℚ n (rowLetters n) Set.univ)) :
    ∀ x, qn_InZ n ν x → qn_InZ n ν (u x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem g hg =>
    rintro x ⟨Y, hY, hx⟩
    rcases hg with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨rowDiv ℤ a b k Y, rowDivStable ℤ n n ν a b k Y hY, by
        rw [qn_T_divPowE n a b hab, hx, lclosedeq_rowDiv_map]⟩
    · exact ⟨rowDiv ℤ a a k Y, rowDivStable ℤ n n ν a a k Y hY, by
        rw [qn_T_binomE, hx, lclosedeq_rowDiv_map]⟩
  | one => intro x hx; exact hx
  | mul g h _ _ ihg ihh => intro x hx; exact ihg _ (ihh x hx)
end Formalism.InvariantFactorPaths.ColumnFamilies
