-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.mem_obd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T18:43:22.464071+00:00
-- url     : https://prove2.me/submissions/d0d7dddc-6269-472b-a6eb-d9db56a06a61

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.mem_obd
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} {p m a : Fin d →₀ ℕ} :
    a ∈ obd d N p m ↔ (∀ k, a k ≤ N) ∧ (∀ k, m k ≤ a k) ∧ ∃ k, N < a k + p k := by

  classical
  rw [obd, Finset.mem_filter, mem_cube_inc]
