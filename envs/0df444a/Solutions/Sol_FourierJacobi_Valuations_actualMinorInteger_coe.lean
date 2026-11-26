-- Prove2me | solution 1 for FourierJacobi.Valuations.actualMinorInteger_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:25.68912+00:00
-- url     : https://prove2.me/submissions/4dbca88f-4512-4a78-8135-b4155f623d94

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a : Kˣ) (x y z : K) :
    (actualMinorInteger v a x y z : WithTop ℤ) =
      matrixMinimum v (secondCompound (g a x y z)) :=
  WithTop.coe_untop _ _
end FourierJacobi.Valuations
