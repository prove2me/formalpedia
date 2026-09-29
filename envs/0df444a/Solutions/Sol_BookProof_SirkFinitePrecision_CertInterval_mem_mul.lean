-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.mem_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T16:09:02.380112+00:00
-- url     : https://prove2.me/submissions/d6519cb9-a2d0-4d9c-ae12-95219a9b88b2

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.mem_mul
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
private theorem mul_bracket_left (c ylo y yhi : ℝ) (h1 : ylo ≤ y) (h2 : y ≤ yhi) :
    min (c * ylo) (c * yhi) ≤ c * y ∧ c * y ≤ max (c * ylo) (c * yhi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩
private theorem mul_bracket_right (xlo x xhi c : ℝ) (h1 : xlo ≤ x) (h2 : x ≤ xhi) :
    min (xlo * c) (xhi * c) ≤ x * c ∧ x * c ≤ max (xlo * c) (xhi * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

set_option maxHeartbeats 1000000 in
theorem solution {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by

  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨h1, h1'⟩ := mul_bracket_left I.lo J.lo y J.hi hy1 hy2
  obtain ⟨h2, h2'⟩ := mul_bracket_left I.hi J.lo y J.hi hy1 hy2
  obtain ⟨h3, h3'⟩ := mul_bracket_right I.lo x I.hi y hx1 hx2
  exact ⟨le_trans (min_le_min h1 h2) h3, le_trans h3' (max_le_max h1' h2')⟩
