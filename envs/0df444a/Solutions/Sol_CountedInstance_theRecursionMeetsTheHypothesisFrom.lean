-- Prove2me | solution 1 for CountedInstance.theRecursionMeetsTheHypothesisFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:01:46.692476+00:00
-- url     : https://prove2.me/submissions/886c674b-5a92-45c9-8634-6079bd2529d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedInstanceStatement
import Definitions.Def_CountedInstance_Pairs
import Definitions.Def_CountedToPadded_GenLevels
import Definitions.Def_PiecesCounted_Half
import Definitions.Def_PiecesCounted_Assume
import Definitions.Def_CountedRecursion_Main
import Definitions.Def_CountedInstance_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cap


set_option autoImplicit false
section
section
open CountedInstance
open Groundwork QueryMachines Printed ExplicitCost
namespace CountedInstance
theorem _root_.solution : TheRecursionMeetsTheHypothesisFrom := by
  intro hB hM hR hG hP
  obtain ⟨c, D₀, Alg₀, h₀, hties⟩ := hB
  obtain ⟨D, Alg, hD, hsame⟩ := hM _ c D₀ Alg₀ h₀
  obtain ⟨C₀, hC₀⟩ := hR (c + 2)
  have hx : 18 ≤ c + 18 := by omega
  have hx2 : c + 7 ≤ 2 ^ (c + 18) := by
    have := Nat.lt_two_pow_self (n := c + 18)
    omega
  have hshort : ∀ lam tr i, D.cap lam tr i ≤ 2 * lam := fun lam => (hsame lam).2.2.2
  obtain ⟨hpoly, hsolves⟩ := hC₀ _ (c + 18) D Alg hD ⟨hD.is, hshort, hx, by omega⟩
  obtain ⟨hL, hK, hN, hE⟩ := hP (c + 18) (max C₀ 10) hx (le_max_right _ _)
  refine ⟨c, c + 18, max C₀ 10, D, Alg, hD, hshort, fun lam hlam => ?_, hx, hx2, hpoly,
    (hG _ _ _ C₀ (max C₀ 10) (fun l => by have := hL.K_two l; omega) (le_max_left _ _)).1 hsolves, hL, hK, hN, hE⟩
  obtain ⟨mu, hmu, hI, hd, hA⟩ := hties lam hlam
  obtain ⟨e1, e2, e3, -⟩ := hsame lam
  refine ⟨mu, hmu, by rw [e2, hI], by rw [e1, hd], fun s hs x y u v => ?_⟩
  rw [e2] at hs
  rw [e3]
  exact (hA s hs).1 x y u v
end CountedInstance
