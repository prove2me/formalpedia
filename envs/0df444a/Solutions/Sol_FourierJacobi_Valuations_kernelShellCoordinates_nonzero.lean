-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelShellCoordinates_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:08.641045+00:00
-- url     : https://prove2.me/submissions/e8022d56-440d-447c-be18-58f4833744c5

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_of_minima
import Theorems.Thm_FourierJacobi_Valuations_actual_minima_integer_nonzero


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (a : Kˣ) (x y z : K)
    (r k j h : ℤ) (c : ℕ) (hr : r ≠ 0)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
    (hc : 2*h = j-r → localFieldValuation K (y^2/(x*z)-1) = ((c:ℤ) : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,z) r k j h c := by
  obtain ⟨he,hm⟩ := actual_minima_integer_nonzero (localFieldValuation K)
    (a:K) x y z r k j h c hr hk hj hh hz hc
  exact kernelShellCoordinates_of_minima K (a,x,y,z) r k j h c he hm
end FourierJacobi.Valuations
