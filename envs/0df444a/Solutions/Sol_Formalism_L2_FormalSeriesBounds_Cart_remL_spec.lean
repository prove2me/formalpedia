-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.remL_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:16.418504+00:00
-- url     : https://prove2.me/submissions/86589ce0-58d7-448c-8c94-f2b340e8b08a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
private theorem vpow_mem_Ty (s : ℕ) {y : ℕ → I ⊕ J → C} (hy : y ∈ X.Ty) : Vpow s y ∈ X.Ty := by
  induction s with
  | zero =>
    have e : Vpow 0 y = y := by
      funext i n
      simp [Vpow]
    rw [e]
    exact hy
  | succ s ih =>
    have e : Vpow (s + 1) y = Vpow 1 (Vpow s y) := by
      funext i n
      simp only [Vpow]
      split_ifs <;> first | rfl | omega | rw [show i - (s + 1) = i - 1 - s by omega]
    rw [e]
    exact X.V_mem _ ih
end Cart
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
end Sys
end Formalism.L2.FormalSeriesBounds
end
end

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
    ∀ s, remL L x s ∈ X.Ty ∧ ∀ j < s, remL L x s j = 0 := by
  intro s
  induction s with
  | zero => exact ⟨hx, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ s ih =>
    obtain ⟨hmemS, hz⟩ := ih
    have hint : ∀ n, V.Ge 0 (remL L x s s n) := X.t2 _ hmemS s hz
    have hL := hmem _ hint
    refine ⟨?_, fun j hj => ?_⟩
    · show remL L x s - Vpow s (L (remL L x s s)) ∈ X.Ty
      exact sub_mem hmemS (vpow_mem_Ty s hL)
    · show remL L x s j - Vpow s (L (remL L x s s)) j = 0
      funext n
      simp only [Pi.sub_apply, Vpow]
      rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj | rfl
      · rw [if_pos hj, hz j hj]
        simp
      · rw [if_neg (lt_irrefl _), Nat.sub_self, hzero]
        simp
end Formalism.L2.FormalSeriesBounds.Cart
