-- Prove2me | solution 1 for FourierJacobi.Valuations.kernelShellCoordinates_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:49.500052+00:00
-- url     : https://prove2.me/submissions/0f1a82e5-4dc2-4c20-8cb2-29f5e308b048

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_of_minima
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum_integer_zero
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum_integer_zero


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (a : Kˣ) (x y : K) (k j h : ℤ)
    (hk : localFieldValuation K (a : K) = (k : WithTop ℤ))
    (hj : localFieldValuation K x = (j : WithTop ℤ))
    (hh : localFieldValuation K y = (h : WithTop ℤ)) :
    KernelShellCoordinates K (a,x,y,0) 0 k j h 0 := by
  apply kernelShellCoordinates_of_minima K (a,x,y,0) 0 k j h 0
  · exact actual_entry_minimum_integer_zero (localFieldValuation K) (a:K) x y k j h
      hk hj hh
  · exact actual_minor_minimum_integer_zero (localFieldValuation K) (a:K) x y k j h 0
      hk hj hh (Units.ne_zero a)
end FourierJacobi.Valuations
