-- Prove2me | solution 1 for Freiman.cert_diagonal_corners_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:18.509805+00:00
-- url     : https://prove2.me/submissions/23513bfe-e8b1-41f6-80f8-2203006883f1

import Theorems.Thm_Freiman_cert_diagonal_corners_from_field_bound
import Theorems.Thm_Freiman_cert_field_lower_bound
import Definitions.Def_Freiman_certDiagonal

open Freiman

theorem solution :
    ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ i j : Fin 2, 0 ≤ certFieldVal (w.corners i j) := by
  exact cert_diagonal_corners_from_field_bound cert_field_lower_bound
