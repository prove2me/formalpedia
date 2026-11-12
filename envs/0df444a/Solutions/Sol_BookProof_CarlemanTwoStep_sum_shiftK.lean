-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sum_shiftK
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-11T06:30:01.003407+00:00
-- url     : https://prove2.me/submissions/1ed25f4b-8799-49cb-b7fb-86a580e46ce1

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sum_shiftK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Theorems.Thm_BookProof_CarlemanTwoStep_mem_innK
import Theorems.Thm_BookProof_CarlemanTwoStep_sub_add_singleK
import Theorems.Thm_BookProof_CarlemanTwoStep_sub_singleK_apply
import Theorems.Thm_BookProof_HermiteCarleman_mem_cube_inc
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i < k → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ innK d N i k, F (b + Finsupp.single i k) := by

  classical
  rw [← Finset.sum_filter_of_ne (p := fun a : Fin d →₀ ℕ => k ≤ a i)
    (fun a _ hne => by by_contra hlt; exact hne (hF a (by omega)))]
  refine Finset.sum_nbij' (fun a => a - Finsupp.single i k) (fun b => b + Finsupp.single i k)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, mem_cube_inc] at ha
    rw [mem_innK]
    refine ⟨fun j => le_trans (by simp [Finsupp.tsub_apply]) (ha.1 j), ?_⟩
    rw [sub_singleK_apply]
    have h2 := ha.1 i
    have h3 := ha.2
    omega
  · intro b hb
    rw [mem_innK] at hb
    simp only [Finset.mem_filter, mem_cube_inc]
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simp; omega
      · simpa [hj] using hb.1 j
    · simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact sub_add_singleK ha.2
  · intro b _; simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [sub_add_singleK ha.2]
