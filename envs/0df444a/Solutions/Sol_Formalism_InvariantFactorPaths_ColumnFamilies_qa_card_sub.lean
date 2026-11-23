-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_card_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:49.463799+00:00
-- url     : https://prove2.me/submissions/983e7115-8505-4073-8267-63bea45a40f0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {T : Finset ℤ} (P : ↥T → Prop) [DecidablePred P]
    [DecidablePred fun d => ∃ h : d ∈ T, P ⟨d, h⟩] :
    (univ.filter P).card = (T.filter fun d => ∃ h : d ∈ T, P ⟨d, h⟩).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext d
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨h, h, hp⟩
  · rintro ⟨_, h, hp⟩; exact ⟨h, hp⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
