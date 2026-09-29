-- Prove2me | solution 1 for Freiman.trunk_boundary_from_factor
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:52:42.712337+00:00
-- url     : https://prove2.me/submissions/1b8b3e30-81fd-476d-9d81-1e55f5a81016

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (hf : ∀ (P : CertPoly22), (∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) → ∀ r s : ℝ, certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s))
    (hb : ∀ z : CertField, (certFieldLower z : ℝ) ≤ certFieldVal z)
    (hscale : ∀ (q : ℚ) (z : CertField), certFieldVal (certFieldScale q z) = (q : ℝ)*certFieldVal z)
    (hc : trunkBoundaryCertificateValid) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s)
    (hp : certPolyEval trunkBoundaryPolynomial r s ≤ 0) :
    r = s := by
  obtain ⟨hanti, -, -, -, h10, h20, h21, -, -⟩ := hc
  rw [hf _ hanti] at hp
  have neg : ∀ z : CertField, 0 < certFieldLower (certFieldScale (-1) z) → certFieldVal z < 0 := by
    intro z hz
    have h1 := hb (certFieldScale (-1) z)
    rw [hscale] at h1
    have h2 : (0:ℝ) < certFieldLower (certFieldScale (-1) z) := by exact_mod_cast hz
    push_cast at h1
    linarith
  have n10 := neg _ h10
  have n20 := neg _ h20
  have n21 := neg _ h21
  have hneg : certFieldVal (trunkBoundaryPolynomial 1 0) +
      certFieldVal (trunkBoundaryPolynomial 2 0)*(r+s) +
      certFieldVal (trunkBoundaryPolynomial 2 1)*r*s < 0 := by
    nlinarith [mul_nonneg hr hs, mul_nonneg (add_nonneg hr hs) (neg_nonneg.2 n20.le),
      mul_nonneg (mul_nonneg hr hs) (neg_nonneg.2 n21.le)]
  by_contra hne
  have hlt : r < s := lt_of_le_of_ne hrs hne
  have hprod : 0 < (r - s) * (certFieldVal (trunkBoundaryPolynomial 1 0) +
      certFieldVal (trunkBoundaryPolynomial 2 0)*(r+s) +
      certFieldVal (trunkBoundaryPolynomial 2 1)*r*s) :=
    mul_pos_of_neg_of_neg (by linarith) hneg
  linarith
