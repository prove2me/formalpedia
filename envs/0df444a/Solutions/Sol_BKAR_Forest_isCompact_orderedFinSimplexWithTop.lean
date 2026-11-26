-- Prove2me | solution 1 for BKAR.Forest.isCompact_orderedFinSimplexWithTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:40.69533+00:00
-- url     : https://prove2.me/submissions/911d022e-8688-4e35-bd2c-d1b4753f7457

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_isClosed_orderedFinSimplexWithTop
import Theorems.Thm_BKAR_Forest_orderedFinSimplexWithTop_subset_pi_Icc

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (top : ℝ) (n : ℕ) :
    IsCompact (orderedFinSimplexWithTop top n) := by
  have hbox :
      IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) top) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  exact IsCompact.of_isClosed_subset hbox
    (isClosed_orderedFinSimplexWithTop top n)
    (orderedFinSimplexWithTop_subset_pi_Icc top n)
end BKAR.Forest
