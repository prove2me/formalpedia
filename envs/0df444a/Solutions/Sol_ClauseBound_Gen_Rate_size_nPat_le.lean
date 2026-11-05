-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_nPat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:50:12.892589+00:00
-- url     : https://prove2.me/submissions/e97e99f6-6deb-4941-a1b6-8276b8f66639

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_nPat_eq
import Theorems.Thm_ClauseBound_Gen_Rate_size_le_self
import Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hP : Par P ρ c) (l lam : ℕ) (hlam : 1 ≤ lam) :
    Nat.size (nPat P (step P x₀ l) lam) ≤ nRectG (g x₀ l) (g x₀ l) * (2 * lam) ^ c + 1 := by
  rw [nPat_eq]
  refine (size_pow_le _ _).trans ?_
  have := (size_le_self (P.cnt 0 lam)).trans (hP.cnt 0 lam hlam)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1
end ClauseBound.Gen.Rate
