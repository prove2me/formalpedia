-- Prove2me | solution 1 for FourierJacobi.Analysis.shell_height_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:45.529617+00:00
-- url     : https://prove2.me/submissions/eb9f3784-3247-4fb6-8362-54f46b76ed21

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_half_cartan_eq
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
namespace FourierJacobi.Analysis
theorem _root_.solution (r k j h c : ℤ) :
    (cartanIndices r k j h c).1 / 2 + (cartanIndices r k j h c).2 =
      -entryMinimum r k j h := by
  rw [half_cartan_eq]
  unfold cartanIndices
  dsimp
  ring
end FourierJacobi.Analysis
