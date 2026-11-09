-- Prove2me | solution 1 for BookProof.CarlemanSimplex.sum_ltermP
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:43:12.505207+00:00
-- url     : https://prove2.me/submissions/a85d5d3e-8749-4490-817b-2087f72a8f60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanSimplex.lean — solution of BookProof.CarlemanSimplex.sum_ltermP
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Theorems.Thm_BookProof_CarlemanSimplex_deg_add
import Theorems.Thm_BookProof_CarlemanSimplex_tsub_add_cancel_of_le_prime
import Theorems.Thm_BookProof_CarlemanSimplex_deg_tsub_of_le
import Theorems.Thm_BookProof_CarlemanSimplex_mem_simplexF
import Theorems.Thm_BookProof_CarlemanSimplex_mem_sInn
import Theorems.Thm_BookProof_CarlemanSimplex_ltermP_shift
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanSimplex




open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

/-- Cancellation of a truncated subtraction below a multi-index.  The platform's
published `ChapterCarlemanSimplex` bundle predates this lemma, and a solution may
not rely on unpublished declarations, so it is proved locally (§5a embed helper). -/
private theorem tsub_cancel_le {P a : Fin d →₀ ℕ} (h : P ≤ a) : a - P + P = a := by
  ext j
  have hj : P j ≤ a j := by
    have := h
    rw [Finsupp.le_def] at this
    exact this j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

set_option maxHeartbeats 1000000 in
theorem solution {w : ℂ} {rc lc : (Fin d →₀ ℕ) → ℝ} {P : Fin d →₀ ℕ}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + P) = rc a)
    (hvan : ∀ a : Fin d →₀ ℕ, ¬ P ≤ a → lc a = 0) (N : ℕ) :
    ∑ a ∈ simplexF d N, ltermP u w lc P a
      = (starRingEnd ℂ) (∑ b ∈ sInn d N (deg P), rtermP u w rc P b) := by

  classical
  have hstep : ∑ a ∈ simplexF d N, ltermP u w lc P a
      = ∑ b ∈ sInn d N (deg P), ltermP u w lc P (b + P) := by
    rw [← Finset.sum_filter_of_ne (p := fun a : Fin d →₀ ℕ => P ≤ a)
      (fun a _ hne => by
        by_contra hle
        exact hne (by rw [ltermP, hvan a hle]; simp))]
    refine Finset.sum_nbij' (fun a => a - P) (fun b => b + P) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, mem_simplexF] at ha
      rw [mem_sInn, deg_tsub_of_le ha.2]
      exact ha.1
    · intro b hb
      rw [mem_sInn] at hb
      simp only [Finset.mem_filter, mem_simplexF]
      refine ⟨by rw [deg_add]; omega, le_add_self⟩
    · intro a ha
      simp only [Finset.mem_filter] at ha
      exact tsub_cancel_le ha.2
    · intro b _; exact add_tsub_cancel_right b P
    · intro a ha
      simp only [Finset.mem_filter] at ha
      rw [tsub_cancel_le ha.2]
  rw [hstep, map_sum]
  exact Finset.sum_congr rfl fun b _ => ltermP_shift hcomp b
