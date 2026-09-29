-- Prove2me | solution 1 for Freiman.trunk_diagonal_polynomial_from_corners
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:55:03.945216+00:00
-- url     : https://prove2.me/submissions/bf29c74a-1cbc-4eb1-bf57-4dc7ada5b774

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (hf : ∀ (P : CertPoly22), (∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) → ∀ r s : ℝ, certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s))
    (hb : ∀ (R : CertRectangle) (A B D : ℝ), certRectangleValid R → (∀ i j : Fin 2, 0 < A+B*((trunkCorner R.r0 R.r1 i : ℝ)+trunkCorner R.s0 R.s1 j)+D*trunkCorner R.r0 R.r1 i*trunkCorner R.s0 R.s1 j) → ∀ r s : ℝ, certRectangleMem R r s → 0 < A+B*(r+s)+D*r*s)
    (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (hc : ∀ i j : Fin 2, 0 < (w.diagonal : ℝ)*(certFieldVal (trunkPolynomial C w 1 0)+certFieldVal (trunkPolynomial C w 2 0)*((trunkCorner w.rectangle.r0 w.rectangle.r1 i : ℝ)+trunkCorner w.rectangle.s0 w.rectangle.s1 j)+certFieldVal (trunkPolynomial C w 2 1)*trunkCorner w.rectangle.r0 w.rectangle.r1 i*trunkCorner w.rectangle.s0 w.rectangle.s1 j))
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) (hs : 0 ≤ (w.diagonal : ℝ)*(r-s)) :
    0 ≤ certPolyEval (trunkPolynomial C w) r s := by
  obtain ⟨-, -, -, -, hrest⟩ := hw
  rw [if_neg hn] at hrest
  obtain ⟨hd, hrv, -, -, -, -, -, -, hanti, -, -⟩ := hrest
  rw [hf _ hanti]
  set A := certFieldVal (trunkPolynomial C w 1 0) with hA
  set B := certFieldVal (trunkPolynomial C w 2 0) with hB
  set D := certFieldVal (trunkPolynomial C w 2 1) with hD
  set d : ℝ := (w.diagonal : ℝ) with hdd
  have hpos := hb w.rectangle (d*A) (d*B) (d*D) hrv (fun i j => by
    have := hc i j
    ring_nf at this ⊢
    linarith) r s hm
  have hd2 : d * d = 1 := by
    rcases hd with h | h <;> simp only [hdd, h] <;> norm_num
  have key : (r - s) * (A + B*(r+s) + D*r*s) = (d*(r-s)) * (d*A + d*B*(r+s) + d*D*r*s) := by
    have : (r - s) * (A + B*(r+s) + D*r*s) = (d*d) * ((r - s) * (A + B*(r+s) + D*r*s)) := by
      rw [hd2, one_mul]
    rw [this]
    ring
  rw [key]
  exact mul_nonneg hs hpos.le
