-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.en_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:24.747903+00:00
-- url     : https://prove2.me/submissions/b9803974-abf6-4a4f-b96c-f70da33c3606

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]
variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)
include hty
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution (g : Fin 2) (t : ZMod d) (c : Fin (X.rkF g t)) : (F.en g t c).1 = t := by
  rw [← hty g (F.en g t c)]
  exact F.en_ty g t c
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
