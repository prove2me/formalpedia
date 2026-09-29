-- Prove2me | solution 1 for Freiman.cert_bernstein_weights
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:05:59.771752+00:00
-- url     : https://prove2.me/submissions/309db7a1-d437-4f82-8e1c-b160ff33cc01

import Theorems.Thm_Freiman_cert_unit_coordinate
import Theorems.Thm_Freiman_cert_basis_partition
import Theorems.Thm_Freiman_cert_tensor_weights_from_basis

open Freiman
open scoped BigOperators

theorem solution :
    ∀ (R : CertRectangle) (r s : ℝ), certRectangleValid R → certRectangleMem R r s → (∀ i j : Fin 3, 0 ≤ certBernsteinWeight R r s i j) ∧ (∑ i : Fin 3, ∑ j : Fin 3, certBernsteinWeight R r s i j) = 1 := by
  intro R r s hR hm
  have hr : (R.r0:ℝ) < R.r1 := by exact_mod_cast hR.1
  have hs : (R.s0:ℝ) < R.s1 := by exact_mod_cast hR.2
  have hru := cert_unit_coordinate _ _ _ hr ⟨hm.1,hm.2.1⟩
  have hsu := cert_unit_coordinate _ _ _ hs ⟨hm.2.2.1,hm.2.2.2⟩
  exact cert_tensor_weights_from_basis R r s (cert_basis_partition _ hru) (cert_basis_partition _ hsu)
