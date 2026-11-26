-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelShell_nonzero_locus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:24.432012+00:00
-- url     : https://prove2.me/submissions/9b77872f-9f0c-403a-bb97-0012fd21b866

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Theorems.Thm_FourierJacobi_Valuations_actual_determinant_valuation
import Theorems.Thm_FourierJacobi_Valuations_nonzero_of_integer_valuation


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (x y z : K) (r j h : ℤ) (c : ℕ)
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ y^2-x*z ≠ 0 := by
  have hd := actual_determinant_valuation (localFieldValuation K) x y z r j h c
    hj hh hz hc
  exact ⟨nonzero_of_integer_valuation _ _ _ hj,
    nonzero_of_integer_valuation _ _ _ hh, nonzero_of_integer_valuation _ _ _ hz,
    nonzero_of_integer_valuation _ _ _ hd⟩
end FourierJacobi.Valuations
