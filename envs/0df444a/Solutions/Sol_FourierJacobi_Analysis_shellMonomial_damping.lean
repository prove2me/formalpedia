-- Prove2me | solution 1 for FourierJacobi.Analysis.shellMonomial_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:47.870219+00:00
-- url     : https://prove2.me/submissions/0f5110cd-530d-4eec-98b2-eb78c7bb78e8

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_shellHeight_eq
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_shell_exponents_nonnegative
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) (r : ℤ)
    (p : ℤ × ℤ × ℤ) (c : ℕ) :
    shellMonomial t d U V T r p c =
      T ^ shellHeight r p * shellMonomial t d U V 1 r p c := by
  have hn := shell_exponents_nonnegative r p.1 p.2.1 p.2.2 c
  have hn' := Int.toNat_of_nonneg hn.1
  have hb' := Int.toNat_of_nonneg hn.2
  rw [shellHeight_eq r p c]
  unfold shellMonomial
  dsimp
  rw [← hn', ← hb']
  simp only [zpow_natCast, Int.toNat_natCast, one_mul, mul_pow, pow_add]
  ring
end FourierJacobi.Analysis
