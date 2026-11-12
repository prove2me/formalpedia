-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.faceK_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T07:38:22.369708+00:00
-- url     : https://prove2.me/submissions/01796576-d308-47bc-ae88-3e5dfb9a352b

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.faceK_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_mem_faceK
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card) ≤ k := by

  classical
  have hsub : ((Finset.range M).filter (fun N => a ∈ faceK d N i k))
      ⊆ Finset.Ico (a i) (a i + k) := by
    intro N hN
    simp only [Finset.mem_filter] at hN
    rw [mem_faceK] at hN
    exact Finset.mem_Ico.mpr ⟨hN.2.1 i, hN.2.2⟩
  calc (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card)
      ≤ (Finset.Ico (a i) (a i + k)).card := Finset.card_le_card hsub
    _ = k := by rw [Nat.card_Ico]; omega
