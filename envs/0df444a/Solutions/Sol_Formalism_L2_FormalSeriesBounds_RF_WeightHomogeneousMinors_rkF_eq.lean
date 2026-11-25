-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.rkF_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:20.732863+00:00
-- url     : https://prove2.me/submissions/10ffd4c1-5477-4727-9d06-192bfed4d515

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
theorem _root_.solution (g : Fin 2) (t : ZMod d) : X.rkF g t = r (tau o0 g t) := by
  unfold RowData.rkF
  have hc : (Finset.univ : Finset (Fin (r (tau o0 g t)))).card = r (tau o0 g t) := by simp
  rw [← hc]
  symm
  apply Finset.card_bij (fun c _ => (⟨t, c⟩ : IIof r tau o0 g))
  · intro c _; simp [hty]
  · intro c1 _ c2 _ h; simpa using h
  · rintro ⟨t', c⟩ hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hty] at hc'
    subst hc'
    exact ⟨c, Finset.mem_univ _, rfl⟩
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
