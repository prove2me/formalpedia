-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.iterate_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:15.748284+00:00
-- url     : https://prove2.me/submissions/5560994a-6332-4dda-99af-209c28ae82b4

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_contracts
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate

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
theorem _root_.solution {a b : C → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) ((D.Psi)^[n] a c - (D.Psi)^[n] b c) := by
  induction n with
  | zero => intro c; exact (ha c).sub (hb c)
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := D.contracts _ _ n (D.noConst_iterate ha n) (D.noConst_iterate hb n) ih c
    have := D.l_ge
    exact OrdGE.mono (by omega) h
end Formalism.BaseCaseIdentities.Data
