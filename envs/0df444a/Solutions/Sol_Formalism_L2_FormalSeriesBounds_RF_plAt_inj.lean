-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.plAt_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:00.896087+00:00
-- url     : https://prove2.me/submissions/c5436e97-7581-4c74-bce5-120b424620c4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {K : Orb → ℕ} {what₂ : ∀ o, Fin (K o) → ℕ} {pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n}
    (h : Function.Injective pl) (o : Orb) : Function.Injective (plAt n pl o) := by
  intro s s' hs
  have h1 := h hs
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
  exact h1
end Formalism.L2.FormalSeriesBounds.RF
