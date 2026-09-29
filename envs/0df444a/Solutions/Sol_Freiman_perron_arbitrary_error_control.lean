-- Prove2me | solution 1 for Freiman.perron_arbitrary_error_control
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:17.633758+00:00
-- url     : https://prove2.me/submissions/d8c9b775-b35e-4451-87f5-4349814b6510

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_perron_rational_comparison_assembly
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_integerDistance_nearest
import Theorems.Thm_Freiman_reduced_denominator_escape
import Theorems.Thm_Freiman_legendre_criterion
import Theorems.Thm_Freiman_continuant_convergent_eq
import Theorems.Thm_Freiman_continuant_coprime
import Theorems.Thm_Freiman_perron_inverse_error

open Freiman

theorem solution (b : ℕ → ℕ+) :
    ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      approximationValue (cfValue b) (q + 1) ≤ 2 ∨
      ∃ n : ℕ, K ≤ n ∧ approximationValue (cfValue b) (q + 1) ≤ perronValue b n := by
  have hc := cf_convergence b
  exact perron_rational_comparison_assembly b hc.2.1 hc.2.2.1 hc.2.2.2.1
    (integerDistance_nearest (cfValue b)) (reduced_denominator_escape (cfValue b) hc.2.1)
    (legendre_criterion b) (continuant_convergent_eq b) (continuant_coprime b) (perron_inverse_error b)
