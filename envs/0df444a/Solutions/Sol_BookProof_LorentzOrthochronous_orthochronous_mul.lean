-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.orthochronous_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:00.936967+00:00
-- url     : https://prove2.me/submissions/cffe14bd-7e4e-4b3e-9537-025d13c0f675

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.orthochronous_mul
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_col
import Theorems.Thm_BookProof_LorentzOrthochronous_lorentz_time_row
import Theorems.Thm_BookProof_LorentzOrthochronous_product_time_component
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution {a b : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : IsLorentz a) (hb : IsLorentz b) (h0a : 0 < a 0 0) (h0b : 0 < b 0 0) :
    0 < (a * b) 0 0 := by

  rw [product_time_component]
  have hra := lorentz_time_row ha
  have hcb := lorentz_time_col hb
  nlinarith [sq_nonneg (a 0 1 * b 1 0 + a 0 2 * b 2 0 + a 0 3 * b 3 0),
    sq_nonneg (a 0 1 * b 2 0 - a 0 2 * b 1 0), sq_nonneg (a 0 1 * b 3 0 - a 0 3 * b 1 0),
    sq_nonneg (a 0 2 * b 3 0 - a 0 3 * b 2 0), mul_pos h0a h0b,
    mul_pos (mul_pos h0a h0b) (mul_pos h0a h0b)]
