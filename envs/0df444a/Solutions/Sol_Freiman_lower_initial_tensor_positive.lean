-- Prove2me | solution 1 for Freiman.lower_initial_tensor_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:58:16.955309+00:00
-- url     : https://prove2.me/submissions/6e6b6e16-6830-4a52-902f-d857aa02d36d

import Theorems.Thm_Freiman_lower_initial_tensor_weights
import Theorems.Thm_Freiman_lower_initial_tensor_reconstruction
import Theorems.Thm_Freiman_lower_initial_tensor_weighted_positive
import Theorems.Thm_Freiman_cert_field_lower_bound
import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (c : LowerInitialSeamCase) (hv : lowerInitialSeamCertificateValid c)
    (x y z : ℝ) (hb : lowerInitialBox x y z) :
    0 < lowerInitialPolyEval (lowerInitialSeamPolynomial c) x y z := by
  rcases hv with ⟨he,hc⟩
  have hw := lower_initial_tensor_weights x y z hb
  rw [lower_initial_tensor_reconstruction, ← he]
  apply lower_initial_tensor_weighted_positive _ x y z _ hw.1 hw.2
  intro i j k
  exact lt_of_lt_of_le (by exact_mod_cast hc i j k)
    (cert_field_lower_bound (lowerInitialSeamCoefficients c i j k))
