-- Prove2me | solution 1 for ClauseBound.Gen.Rate.nPat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:05.481664+00:00
-- url     : https://prove2.me/submissions/17b2f02d-a1b3-4fc9-92af-f394177bd3c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
import Theorems.Thm_ClauseBound_Gen_Rate_nPat_eq
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * nRectG (g x₀ l) (g x₀ l)) := by
  rw [nPat_eq, pow_mul]
  exact Nat.pow_le_pow_left ((hP.cnt 0 lam hlam).trans (Nat.pow_le_pow_left (two_lam_le hx l lam B) c)) _
end ClauseBound.Gen.Rate
