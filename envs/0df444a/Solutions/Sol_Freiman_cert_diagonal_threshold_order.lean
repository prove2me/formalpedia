-- Prove2me | solution 1 for Freiman.cert_diagonal_threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:18.745447+00:00
-- url     : https://prove2.me/submissions/f3ed9662-88c8-426c-bd67-be6556aae235

import Theorems.Thm_Freiman_cert_diagonal_order_from_factors
import Theorems.Thm_Freiman_cert_diagonal_factorization
import Theorems.Thm_Freiman_cert_diagonal_bilinear_interpolation
import Theorems.Thm_Freiman_cert_diagonal_corners_nonnegative
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_cross_polynomial
import Theorems.Thm_Freiman_cert_threshold_cross_order
import Theorems.Thm_Freiman_cert_threshold_denominator_positive
import Definitions.Def_Freiman_certDiagonal

open Freiman

theorem solution :
    ∀ (w : CertDiagonalData), certDiagonalDataValid w → ∀ r s : ℝ, certRectangleMem w.rectangle r s → certDiagonalSide w r s → certThresholdVal w.upperThreshold r s ≤ certThresholdVal w.lowerThreshold r s := by
  exact cert_diagonal_order_from_factors cert_diagonal_factorization cert_diagonal_bilinear_interpolation cert_diagonal_corners_nonnegative cert_field_lower_bound cert_cross_polynomial cert_threshold_cross_order cert_threshold_denominator_positive
