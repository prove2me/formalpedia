-- Prove2me | solution 1 for Formalism.REAL.CharId_Mpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:40.251619+00:00
-- url     : https://prove2.me/submissions/dacf40c1-01cf-4b08-a795-4ba8643712ab

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_M_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (y : Fin n → V) (a : Fin n) :
    (CharId_M E ^ k) y a = ∑ b, epow E k a b (y b) := by
  induction k generalizing y with
  | zero =>
    have h0 : ∀ b, epow E 0 a b (y b) = if a = b then y b else 0 := by
      intro b
      simp only [epow]
      split_ifs <;> simp
    simp [h0]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [epow, CharId_M_apply, map_sum, LinearMap.sum_apply,
      Module.End.mul_apply]
    exact Finset.sum_comm
end Formalism.REAL
