-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.coeff_iterate_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:45.046012+00:00
-- url     : https://prove2.me/submissions/0b758b1c-ae0d-4a2f-ad51-f63745f65600

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_iterate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_iterate_close
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_iterate_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero


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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
namespace Formalism.L2.FormalSeriesBounds.Contr
theorem _root_.solution (c : B) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A (Ψ^[n] 0 c) = coeff A (H.fixPt c) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : coeff A (H.fixPt c) = coeff A (Ψ^[A.degree] 0 c) := rfl
  have h1 := H.iterate_close (a := Ψ^[j] 0) (b := 0) (H.noConst_iterate noConst_zero j)
    noConst_zero A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h1
  rw [Function.iterate_add_apply, e]
  exact h1
end Formalism.L2.FormalSeriesBounds.Contr
