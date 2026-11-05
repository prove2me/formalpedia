-- Prove2me | solution 1 for ClauseBound.Gen.Rate.pot_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:06.867874+00:00
-- url     : https://prove2.me/submissions/18736fb5-9af4-49ba-af61-b113a92b39e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_c_pos
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_nPat_le
import Theorems.Thm_ClauseBound_Gen_Rate_X_cast
import Theorems.Thm_ClauseBound_Gen_Rate_pot_step
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le
import Theorems.Thm_ClauseBound_Gen_Rate_rest_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_cast_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B cnt z : ℕ) (hlam : 1 ≤ lam) :
    (Nat.size (z + nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam) + Nat.size (cnt * nPat P (step P x₀ l) lam) + (g x₀ l * g x₀ l) ^ 2 * lam +
      g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1) + 2 + Nat.size (cnt * nPat P (step P x₀ l) lam)) : ℝ) ≤
      Nat.size (z + Nat.size cnt) + 1 + ((c + 3) * Real.logb 2 ((K x₀ (l + 1) : ℝ) * (lam + B)) + 1) := by
  have n3 := big_le_K hx l
  have n4 := K_le_g x₀ l
  have hX1 : 1 ≤ g x₀ l ^ 2 * (lam + B) := by have := two_lam_le hx l lam B; omega
  have hR : nRectG (g x₀ l) (g x₀ l) ≤ g x₀ l ^ 4 := by have := four_nRect_le (g x₀ l); omega
  have H2 := Nat.cast_le (α := ℝ).2 (pot_step z cnt (nPat P (step P x₀ l) lam) (nRectG (g x₀ l) (g x₀ l) * Nat.size (P.d 0 lam))
    ((g x₀ l * g x₀ l) ^ 2 * lam) (g x₀ l ^ 2 * (g x₀ l * B + g x₀ l ^ 2 * P.bits 0 lam + 1)))
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at H2
  have H2r := size_cast_le hX1 (rest_le (g x₀ l) c lam B (P.bits 0 lam) (Nat.size (P.d 0 lam)) (nRectG (g x₀ l) (g x₀ l))
    (Nat.size (nPat P (step P x₀ l) lam)) (c_pos hP) hlam (by omega) (hP.bits 0 lam hlam) (Nat.size_le.2 (hP.d 0 lam hlam)) hR
    (size_nPat_le hP l lam hlam))
  rw [X_cast, Nat.cast_add, Nat.cast_ofNat] at H2r
  linarith
end ClauseBound.Gen.Rate
