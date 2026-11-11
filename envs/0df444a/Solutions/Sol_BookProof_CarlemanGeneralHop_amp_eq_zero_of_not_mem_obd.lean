-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T18:49:31.576209+00:00
-- url     : https://prove2.me/submissions/b5895c5a-35e2-456a-ae2e-c90cb01db4b9

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.amp_eq_zero_of_not_mem_obd
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_apply
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_hopB
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_obd
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
theorem solution {N : ℕ} {p m : Fin d →₀ ℕ} {c : (Fin d →₀ ℕ) → ℝ}
    (hvanR : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, m k ≤ a k) → c a = 0) {a : Fin d →₀ ℕ}
    (ha : a ∈ cube d N \ hopB (cube d N) p m) (hne : a ∉ obd d N p m) : c a = 0 := by

  classical
  rw [Finset.mem_sdiff] at ha
  by_cases hm : ∀ k, m k ≤ a k
  · exfalso
    refine hne (mem_obd.mpr ⟨mem_cube_inc.mp ha.1, hm, ?_⟩)
    have hnot : hshift p m a ∉ cube d N := fun hc => ha.2 (mem_hopB.mpr ⟨hm, hc⟩)
    rw [mem_cube_inc] at hnot
    push_neg at hnot
    obtain ⟨k, hk⟩ := hnot
    rw [hshift_apply] at hk
    have := hm k
    exact ⟨k, by omega⟩
  · exact hvanR a hm
