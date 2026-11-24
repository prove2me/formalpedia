-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.expansionL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:05.913269+00:00
-- url     : https://prove2.me/submissions/1d5f6515-a214-4970-aa2a-fa120761ee5d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_remL_spec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_remL_eq

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution (hmem : ∀ h, (∀ n, V.Ge 0 (h n)) → L h ∈ X.Ty) (hzero : ∀ h, L h 0 = h)
    {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) :
    ∃ h : ℕ → I ⊕ J → C, (∀ s n, V.Ge 0 (h s n)) ∧ x = sumV (fun s => L (h s)) := by
  refine ⟨fun s => remL L x s s,
    fun s n => X.t2 _ (remL_spec hmem hzero hx s).1 s (remL_spec hmem hzero hx s).2 n, ?_⟩
  funext i n
  have h0 := (remL_spec hmem hzero hx (i + 1)).2 i (Nat.lt_succ_self i)
  rw [remL_eq] at h0
  have h1 := congrFun h0 n
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [sumV]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Vpow]
  rw [if_neg (by simp at hs; omega)]
end Formalism.L2.FormalSeriesBounds.Cart
