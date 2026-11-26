-- Prove2me | solution 1 for FourierJacobi.Analysis.masterTerm_norm_le_undamped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:13.565221+00:00
-- url     : https://prove2.me/submissions/c7a5d038-12d6-43d7-801d-6b7df867bf48

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_damping
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V : ℂ) (r : ℤ)
    (p : LatticeIndex) {T : ℝ} (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1) :
    ‖masterTerm q t d U V (T : ℂ) r p‖ ≤ ‖masterTerm q t d U V 1 r p‖ := by
  rw [masterTerm_damping, norm_mul, norm_pow]
  have ht : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT₀]
  rw [ht]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hT₀ hT₁)
end FourierJacobi.Analysis
