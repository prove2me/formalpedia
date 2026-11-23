-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_iterate_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:55:36.144174+00:00
-- url     : https://prove2.me/submissions/8f0bf142-d5d1-4e0c-90f6-f5a59d380c03

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_iterate_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (c : C) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A ((D.Psi)^[n] 0 c) = coeff A (D.fixPt c) := by
  have e : coeff A (D.fixPt c) = coeff A ((D.Psi)^[A.degree] 0 c) := rfl
  rw [e]
  have hn' : n = A.degree + (n - A.degree) := by omega
  rw [hn', Function.iterate_add_apply]
  have h := D.iterate_close (D.noConst_iterate noConst_zero (n - A.degree)) noConst_zero
    A.degree c A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h
  exact h
end Formalism.BaseCaseIdentities.Data
