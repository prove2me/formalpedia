-- Prove2me | solution 1 for BookProof.CarlemanSimplex.sum_mterm_conj
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:09:17.266832+00:00
-- url     : https://prove2.me/submissions/689835b6-7b2d-456b-8086-d34c0bfc206b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.sum_mterm_conj
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
import Theorems.Thm_BookProof_CarlemanSimplex_rcm_of_zero
import Theorems.Thm_BookProof_CarlemanSimplex_deg_shiftm
import Theorems.Thm_BookProof_CarlemanSimplex_rcm_shiftm
import Theorems.Thm_BookProof_CarlemanSimplex_shiftm_apply_self
import Theorems.Thm_BookProof_CarlemanSimplex_shiftm_shiftm
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {M : Fin d → Fin d → ℂ} (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (N : ℕ) (i j : Fin d) :
    (starRingEnd ℂ) (∑ a ∈ simplexF d N, mterm u M a i j)
      = ∑ b ∈ simplexF d N, mterm u M b j i := by

  classical
  rw [map_sum]
  -- restrict both sides to the multi-indices where the amplitude does not vanish
  have hL : ∑ a ∈ simplexF d N, (starRingEnd ℂ) (mterm u M a i j)
      = ∑ a ∈ (simplexF d N).filter (fun a => 1 ≤ a j),
          (starRingEnd ℂ) (mterm u M a i j) := by
    refine (Finset.sum_filter_of_ne fun a _ hne => ?_).symm
    by_contra hlt
    have h0 : a j = 0 := by omega
    rw [mterm, rcm_of_zero h0] at hne
    simp at hne
  have hR : ∑ b ∈ simplexF d N, mterm u M b j i
      = ∑ b ∈ (simplexF d N).filter (fun b => 1 ≤ b i), mterm u M b j i := by
    refine (Finset.sum_filter_of_ne fun b _ hne => ?_).symm
    by_contra hlt
    have h0 : b i = 0 := by omega
    rw [mterm, rcm_of_zero h0] at hne
    simp at hne
  rw [hL, hR]
  refine Finset.sum_nbij' (fun a => shiftm a i j) (fun b => shiftm b j i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, mem_simplexF] at ha ⊢
    refine ⟨by rw [deg_shiftm ha.2]; exact ha.1, ?_⟩
    rw [shiftm_apply_self]
    omega
  · intro b hb
    simp only [Finset.mem_filter, mem_simplexF] at hb ⊢
    refine ⟨by rw [deg_shiftm hb.2]; exact hb.1, ?_⟩
    rw [shiftm_apply_self]
    omega
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact shiftm_shiftm ha.2
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact shiftm_shiftm hb.2
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [mterm, mterm, rcm_shiftm ha.2, shiftm_shiftm ha.2, hM i j]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
