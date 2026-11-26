-- Prove2me | solution 1 for FourierJacobi.Analysis.i0NegativeRowEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:08.626555+00:00
-- url     : https://prove2.me/submissions/180562d7-4e6a-4935-8c0e-147d518bfdbe

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (tail : Bool) (n : ℕ × ℕ × ℕ) :
    (i0NegativeRowEquiv tail n).val = (-(n.1 : ℤ) - 1, (n.2.1 : ℤ),
      if tail then -(n.2.2 : ℤ) - 1 else (n.2.2 : ℤ)) := rfl
end FourierJacobi.Analysis
