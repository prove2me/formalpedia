-- Prove2me | solution 1 for Eight.ViaGrouping.levelNetP_isNetworkP_printed_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:38.427647+00:00
-- url     : https://prove2.me/submissions/09c335e6-20d7-40bf-969a-6fef7217ccaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_Eight_ViaGrouping_isNetworkP_mono_B
import Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP_of

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by
  obtain ⟨a, -, ha⟩ := levelNetP_isNetworkP_of hPr g hg
  refine ⟨a, fun tr psi hΨ C _ lam R c B t S Rm y hl ht hy hR => isNetworkP_mono_B (ha tr psi hΨ C lam R c B t S Rm y hl ht hy hR) ?_⟩
  have : g ^ 2 * tOf (lam c) ≤ g ^ 2 * lam c := Nat.mul_le_mul_left _ (by unfold tOf; omega)
  omega
end Eight.ViaGrouping
