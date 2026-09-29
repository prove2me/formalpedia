-- Prove2me | solution 1 for Freiman.cert_diagonal_order_from_factors
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:23:58.319825+00:00
-- url     : https://prove2.me/submissions/c72b9108-a972-45cd-b4cd-18915d3d20aa

import Definitions.Def_Freiman_certDiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Freiman

theorem solution :
    (∀ (a b c : CertField) (r s : ℝ), certPolyEval (certDiagonalPolynomial a b c) r s = (r-s)*certDiagonalFactor a b c r s) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → (∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j)) → ∀ r s : ℝ, certRectangleMem w.rectangle r s → 0 ≤ (if w.positiveDirection then (1:ℝ) else -1)*certDiagonalFactor w.a w.b w.c r s) → (∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j)) → (∀ z : CertField, (certFieldLower z:ℝ) ≤ certFieldVal z) → (∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r) → (∀ (l u : CertThreshold) (r s : ℝ), 0 < certThresholdDen l r → 0 < certThresholdDen u r → (0 ≤ certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s ≤ certThresholdVal l r s) ∧ (0 < certThresholdNum l s*certThresholdDen u r-certThresholdNum u s*certThresholdDen l r ↔ certThresholdVal u r s < certThresholdVal l r s)) → (∀ (t : CertThreshold) (r : ℝ), 0 ≤ r → 0 ≤ certFieldVal t.x0 → 0 ≤ certFieldVal t.x1 → 0 < certThresholdDen t r) → ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s := by
  intro hfactor hinterp hcorners hlower hcross horder hden w hw r s hmem hside
  have hparts := hw
  rcases hparts with ⟨_, hr0, hl, hu, hpoly, _, _⟩
  have hr0' : (0 : ℝ) ≤ (w.rectangle.r0 : ℝ) := by exact_mod_cast hr0
  have hr : 0 ≤ r := hr0'.trans hmem.1
  have lower_nonneg (t : CertThreshold) (ht : certThresholdDataValid t) :
      0 ≤ certFieldVal t.x0 ∧ 0 ≤ certFieldVal t.x1 := by
    constructor
    · have h : (0 : ℝ) ≤ (certFieldLower t.x0 : ℝ) := by exact_mod_cast ht.1
      exact h.trans (hlower t.x0)
    · have h : (0 : ℝ) ≤ (certFieldLower t.x1 : ℝ) := by exact_mod_cast ht.2
      exact h.trans (hlower t.x1)
  have hln := lower_nonneg w.lowerThreshold hl
  have hun := lower_nonneg w.upperThreshold hu
  apply (horder w.lowerThreshold w.upperThreshold r s
    (hden _ _ hr hln.1 hln.2) (hden _ _ hr hun.1 hun.2)).1.mp
  rw [← hcross, hpoly, hfactor]
  have hf := hinterp w hw (hcorners w hw) r s hmem
  cases hd : w.positiveDirection with
  | false =>
    have hs : r ≤ s := by simpa [certDiagonalSide, hd] using hside
    have hf' : certDiagonalFactor w.a w.b w.c r s ≤ 0 := by simpa [hd] using hf
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hs) hf'
  | true =>
    have hs : s ≤ r := by simpa [certDiagonalSide, hd] using hside
    have hf' : 0 ≤ certDiagonalFactor w.a w.b w.c r s := by simpa [hd] using hf
    exact mul_nonneg (sub_nonneg.mpr hs) hf'

#print axioms solution
