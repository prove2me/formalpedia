-- Prove2me | solution 1 for BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T10:24:25.074474+00:00
-- url     : https://prove2.me/submissions/6f6bcb54-80be-4f44-9894-5be75f1248aa

-- Generated from ChapterHilbertSumIntertwine.lean — solution of BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine
import Mathlib
import Definitions.Def_ChapterHilbertSumIntertwine
import Theorems.Thm_BookProof_ChapterHilbertSumIntertwine_memLp_fibrewise
open BookProof.ChapterHilbertSumIntertwine



open scoped InnerProductSpace



variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

set_option maxHeartbeats 1000000 in
theorem solution {V : ∀ i, G i →ₗᵢ[ℂ] H} (hsum : IsHilbertSum ℂ G V)
    (A : H →L[ℂ] H) (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (hcomm : ∀ i u, V i (B i u) = A (V i u)) (v : H) (i : ι) :
    hsum.linearIsometryEquiv (A v) i = B i (hsum.linearIsometryEquiv v i) := by

  set w := hsum.linearIsometryEquiv v with hw
  have hmem : Memℓp (fun i => B i (w i)) 2 := memLp_fibrewise B hB w
  set w' : lp G 2 := ⟨_, hmem⟩ with hw'
  have hsymm : hsum.linearIsometryEquiv.symm w' = A v := by
    have h1 : HasSum (fun i => V i (w' i)) (hsum.linearIsometryEquiv.symm w') :=
      hsum.hasSum_linearIsometryEquiv_symm w'
    have h2 : HasSum (fun i => V i (w i)) (hsum.linearIsometryEquiv.symm w) :=
      hsum.hasSum_linearIsometryEquiv_symm w
    have h3 : HasSum (fun i => A (V i (w i))) (A (hsum.linearIsometryEquiv.symm w)) :=
      h2.mapL A
    have h5 : HasSum (fun i => V i (w' i)) (A (hsum.linearIsometryEquiv.symm w)) := by
      refine h3.congr_fun ?_
      intro i
      exact hcomm i (w i)
    have h6 : hsum.linearIsometryEquiv.symm w' = A (hsum.linearIsometryEquiv.symm w) :=
      h1.unique h5
    rw [h6, hw, LinearIsometryEquiv.symm_apply_apply]
  have hA : hsum.linearIsometryEquiv (A v) = w' := by
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  rw [hA]
