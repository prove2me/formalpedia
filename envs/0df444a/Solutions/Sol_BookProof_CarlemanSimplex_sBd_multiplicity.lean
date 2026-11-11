-- Prove2me | solution 1 for BookProof.CarlemanSimplex.sBd_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:12:01.059194+00:00
-- url     : https://prove2.me/submissions/67d763b3-a682-448c-9962-8952d4d83ce5

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.sBd_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_mem_sBd
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card) ≤ k := by

  classical
  have hsub : ((Finset.range M).filter (fun N => a ∈ sBd d N k))
      ⊆ Finset.Ico (deg a) (deg a + k) := by
    intro N hN
    simp only [Finset.mem_filter] at hN
    rw [mem_sBd] at hN
    exact Finset.mem_Ico.mpr ⟨hN.2.1, hN.2.2⟩
  calc (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card)
      ≤ (Finset.Ico (deg a) (deg a + k)).card := Finset.card_le_card hsub
    _ = k := by rw [Nat.card_Ico]; omega
