-- Prove2me | solution 1 for FourierJacobi.Algebra.coe_pow_norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:56.556831+00:00
-- url     : https://prove2.me/submissions/f3cddaf3-4009-4f9c-82d8-f8ae4ebfbf38

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {n : ℕ} (hn : n ≠ 0) : ‖(t : ℂ) ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (coe_norm_lt_one ht₀ ht₁) hn
end FourierJacobi.Algebra
