-- Prove2me | solution 1 for FamousTheorems.vandermonde_determinant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:13:48.77088+00:00
-- url     : https://prove2.me/submissions/a6260f1b-1dd6-400a-a326-4d2b0bf11adb

import Mathlib

theorem solution {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j > i, (v j - v i) :=
  Matrix.det_vandermonde v
