-- Prove2me | solution 1 for FourierJacobi.Analysis.normalized_intertwiner_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:16.349796+00:00
-- url     : https://prove2.me/submissions/04aad2e9-8d12-401c-b52e-2e3fef0ea226

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative
import Theorems.Thm_FourierJacobi_Analysis_intertwiner_entry_derivative

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) :
    (fun i j => -(q - 1) / (2 * Real.log q) *
      deriv (fun s => intertwinerFamily q s i j) (1 / 2)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hq₁ : q - 1 ≠ 0 := by linarith
  have hl : Real.log q ≠ 0 := ne_of_gt (Real.log_pos hq)
  ext i j
  rw [(intertwiner_entry_derivative q hq i j).deriv]
  field_simp
end FourierJacobi.Analysis
