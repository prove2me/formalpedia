-- Prove2me | solution 1 for ClauseBound.Alg.Enum.cap_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:48:57.332933+00:00
-- url     : https://prove2.me/submissions/1feb647d-4f62-4b73-8e91-b1e6718bc0a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_Network_lab_comm
import Theorems.Thm_Groundwork_card_words


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
namespace ClauseBound.Alg.Enum
theorem _root_.solution (hN : F.toP.Presents c N 0 0) (a b : Fin g) (hab : a ≠ b) : F.cap c a b = F.cap c b a := by
  have h : words (F.cap c a b) = words (F.cap c b a) := by
    rw [← show N.lab a b = words (F.cap c a b) from hN.lab_eq a b hab, N.lab_comm]
    exact hN.lab_eq b a hab.symm
  have h2 := congrArg card h
  rw [card_words, card_words] at h2
  exact Nat.pow_right_injective le_rfl h2
end ClauseBound.Alg.Enum
