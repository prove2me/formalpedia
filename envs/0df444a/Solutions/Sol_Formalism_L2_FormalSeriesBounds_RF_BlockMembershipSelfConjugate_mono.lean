-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.BlockMembershipSelfConjugate.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:46:11.095212+00:00
-- url     : https://prove2.me/submissions/dfa0743b-852c-4c03-b028-e1c1d91e6994

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.RF
namespace BlockMembershipSelfConjugate
theorem _root_.solution {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod 2 → ℕ → ℕ}
    (h : BlockMembershipSelfConjugate X n F FF gaC) (hs : FF ⊆ FF') : BlockMembershipSelfConjugate X n F FF' gaC :=
  fun L h1 h2 pl hpl => hs (h L h1 h2 pl hpl)
end BlockMembershipSelfConjugate
end Formalism.L2.FormalSeriesBounds.RF
