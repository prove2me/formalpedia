-- Prove2me | solution 1 for Freiman.lower_initial_tensor_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:03.865869+00:00
-- url     : https://prove2.me/submissions/0e9efda3-6794-43a5-be66-39b99a8032ef

import Theorems.Thm_Freiman_lower_initial_tensor_reconstruction_from_field
import Theorems.Thm_Freiman_cert_field_add
import Theorems.Thm_Freiman_cert_field_scale
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (P : LowerInitialPoly) (x y z : ℝ) : lowerInitialPolyEval P x y z = lowerInitialBernsteinEval (lowerInitialBernstein P) x y z := by
  exact lower_initial_tensor_reconstruction_from_field cert_field_add cert_field_scale P x y z
