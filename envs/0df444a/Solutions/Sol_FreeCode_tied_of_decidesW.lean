-- Prove2me | solution 1 for FreeCode.tied_of_decidesW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:49.916761+00:00
-- url     : https://prove2.me/submissions/e3bde33b-bdbc-4db1-b278-7bfe8d2a441d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_FreeCode_Tied
import Theorems.Thm_FreeCode_decidesFree_mono
import Theorems.Thm_FreeCode_decidesTM_of_simulates
import Theorems.Thm_FreeCode_readFree_polyT
import Theorems.Thm_FreeCode_reads_readFree
import Theorems.Thm_FreeCode_stBehindReader
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_exists_simulates


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat
namespace FreeCode
theorem _root_.solution {w : ℕ} {δ : ℝ} (hδ : 0 < δ) {D : StepMachine (List Unit × Fml) Bool} (hp : PolyTimeSteps D) {c₀ : ℕ} (hD : DecidesW w D (δ / 2) c₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ PolyTimeSteps (Stepped.mapIn readFree D) ∧
      DecidesFree (Stepped.mapIn readFree D) w δ c ∧ Simulates M (Stepped.mapIn readFree D) q ∧ SatFree.DecidesTM w M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hp' : PolyTimeSteps (Stepped.mapIn readFree D) := by
    obtain ⟨h⟩ := hp
    exact ⟨IsPolyT.mapIn readFree_polyT⟩
  have hd := stBehindReader readFree reads_readFree w D (δ / 2) c₀ hD
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp'
  obtain ⟨C, hcC, hTM⟩ := FreeCode.decidesTM_of_simulates hδ hs hd
  exact ⟨M, C, q, hfin, hp', decidesFree_mono (by linarith) hcC hd, hs, hTM⟩
end FreeCode
