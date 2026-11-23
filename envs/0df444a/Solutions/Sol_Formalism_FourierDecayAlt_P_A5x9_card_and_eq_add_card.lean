-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.card_and_eq_add_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:46.603364+00:00
-- url     : https://prove2.me/submissions/29c6182d-74f4-49a1-986b-e11ea61aabee

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {α : Type} [Finite α] (A B C : α → Prop) (hBC : ∀ x, C x → B x) :
    Nat.card {x // A x ∧ B x} =
      Nat.card {x // A x ∧ C x} + Nat.card {x // A x ∧ B x ∧ ¬ C x} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨ha, hb⟩
      by_cases hc : C x
      · exact Or.inl ⟨ha, hc⟩
      · exact Or.inr ⟨ha, hb, hc⟩
    · rintro (⟨ha, hc⟩ | ⟨ha, hb, _⟩)
      · exact ⟨ha, hBC x hc⟩
      · exact ⟨ha, hb⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx'.2.2 hx.2
end Formalism.FourierDecayAlt.P.A5x9
