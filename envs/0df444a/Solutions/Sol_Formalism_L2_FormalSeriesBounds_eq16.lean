-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.eq16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:10.68417+00:00
-- url     : https://prove2.me/submissions/a4dd240b-7e5a-444f-afca-353268e8af82

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound_one

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
end Cart
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
end Sys
private theorem ge_mono' {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a :=
  le_trans (WithTop.coe_le_coe.mpr hw) h
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (X : Cart V d I J) : Eq16 X := by
  intro a u x hx i hi
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · obtain rfl : i = 1 := by omega
    refine ⟨fun k => ?_, fun κ => ?_⟩
    · rw [hx.2 k]
      show ((_ : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_mono' (hx.bound_one _) (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    refine ⟨fun k => ge_mono' (hx.bound j _) (by push_cast; linarith),
      fun κ => ge_mono' (hx.bound j _) (by push_cast; linarith [le_max_right (1 : ℝ) ((j : ℝ) + 2 - 1)])⟩
end Formalism.L2.FormalSeriesBounds
