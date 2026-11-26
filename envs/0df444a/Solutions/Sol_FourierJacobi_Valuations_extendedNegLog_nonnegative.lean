-- Prove2me | solution 1 for FourierJacobi.Valuations.extendedNegLog_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:47.103441+00:00
-- url     : https://prove2.me/submissions/7c1fc480-2370-4c43-90f1-730da3c472e9

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
import Definitions.Def_FourierJacobi_Valuations_LocalField

set_option autoImplicit false
noncomputable section
open scoped WithZero
open FourierJacobi FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (x : ℤᵐ⁰) :
    0 ≤ extendedNegLog x ↔ x ≤ 1 := by
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp n =>
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) ↔
      WithZero.exp n ≤ WithZero.exp (0 : ℤ)
    rw [WithTop.coe_le_coe, WithZero.exp_le_exp]
    omega
end FourierJacobi.Valuations
