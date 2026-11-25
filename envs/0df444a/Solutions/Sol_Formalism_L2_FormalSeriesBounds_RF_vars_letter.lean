-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.vars_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:32.17507+00:00
-- url     : https://prove2.me/submissions/ac03d85b-365c-4a61-a3f4-0ae33ee673fd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by
  obtain ⟨x, -, e⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)
  have e2 : (⟨g, F.en g a x.2⟩ : WV I) = w := congrArg Prod.snd e
  subst e2
  exact ⟨rfl, F.en_ty g a x.2⟩
end Formalism.L2.FormalSeriesBounds.RF
