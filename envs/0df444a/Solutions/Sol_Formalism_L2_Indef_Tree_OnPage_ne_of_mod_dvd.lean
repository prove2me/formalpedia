-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.ne_of_mod_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:54:05.140795+00:00
-- url     : https://prove2.me/submissions/f5bc35a0-acc1-4356-9c93-5fdd3851e6fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution {g a M : ℕ} (h : g % M = 1) (ha : a ∣ M) (ha1 : 1 < a) : a ≠ g := by
  intro hag
  rw [hag] at ha ha1
  have h2 := Nat.mod_mod_of_dvd g ha
  rw [h, Nat.mod_self, Nat.mod_eq_of_lt ha1] at h2
  exact absurd h2 (by norm_num)
end Formalism.L2.Indef.Tree.OnPage
