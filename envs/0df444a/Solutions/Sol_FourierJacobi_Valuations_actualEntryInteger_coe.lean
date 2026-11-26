-- Prove2me | solution 1 for FourierJacobi.Valuations.actualEntryInteger_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:21.587202+00:00
-- url     : https://prove2.me/submissions/e8e0d573-8cec-42c3-90fe-2c8b79f2186c

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
    (actualEntryInteger v a x y z : WithTop ℤ) = matrixMinimum v (g a x y z) :=
  WithTop.coe_untop _ _
end FourierJacobi.Valuations
