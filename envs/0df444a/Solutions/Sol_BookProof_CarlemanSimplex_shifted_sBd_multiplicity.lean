-- Prove2me | solution 1 for BookProof.CarlemanSimplex.shifted_sBd_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:12:02.600336+00:00
-- url     : https://prove2.me/submissions/93c08efa-a1b1-4ee4-b9ed-1ed97e4ab61e

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.shifted_sBd_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_deg_add
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
theorem solution (P : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card) ≤ deg P := by

  classical
  have hsub : ((Finset.range M).filter
        (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P)))
      ⊆ Finset.Ico (deg b - deg P) (deg b) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_image] at hN
    obtain ⟨a, ha, hab⟩ := hN.2
    rw [mem_sBd] at ha
    have hbd : deg b = deg a + deg P := by rw [← hab, deg_add]
    refine Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  calc (((Finset.range M).filter
        (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card)
      ≤ (Finset.Ico (deg b - deg P) (deg b)).card := Finset.card_le_card hsub
    _ ≤ deg P := by rw [Nat.card_Ico]; omega
