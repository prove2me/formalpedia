-- Prove2me | solution 1 for Coding.eq_of_lex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:45.13586+00:00
-- url     : https://prove2.me/submissions/5a0895ca-45ad-49d0-a303-b4b997ee0d3e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
namespace Coding
theorem _root_.solution {l₁ l₂ : List (ℕ × ℕ)} (h₁ : l₁.Pairwise lexLt) (h₂ : l₂.Pairwise lexLt) (h : ∀ q, q ∈ l₁ ↔ q ∈ l₂) : l₁ = l₂ := by
  have irr : ∀ {a b : ℕ × ℕ}, lexLt a b → a ≠ b := by
    intro a b hab e
    subst e
    unfold lexLt at hab
    omega
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => ?_) h₁ h₂ ((List.perm_ext_iff_of_nodup (h₁.imp irr) (h₂.imp irr)).2 h)
  unfold lexLt at hab hba
  omega
end Coding
