-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Group.ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:16.732162+00:00
-- url     : https://prove2.me/submissions/42590b34-84b0-4385-8bdd-71e934f78b46

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_not_four_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Group
namespace Formalism.FrobeniusOrbits.Group
theorem _root_.solution (l : ℤ) (hl : Odd l) (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    ((2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ M ∣ l - 1 ∨ (2 : ℤ) ^ M ∣ l + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have hx : Odd (l ^ (2 ^ j)) := hl.pow
    have e : l ^ (2 ^ (j + 1)) = (l ^ (2 ^ j)) ^ 2 := by
      rw [show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
    have hK : M + (j + 1) = M + j + 1 := by omega
    rw [e, hK]
    have h4 : ¬ (2 : ℤ) ^ (M + j + 1) ∣ (l ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply not_four_dvd _ hx
      refine dvd_trans ?_ h
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    rw [or_iff_left h4, ← key _ hx _ (by omega)]
    have e6 : (l ^ (2 ^ j)) ^ 2 - 1 = (l ^ (2 ^ j) - 1) * (l ^ (2 ^ j) + 1) := by ring
    rw [e6]
end Formalism.FrobeniusOrbits.Group
