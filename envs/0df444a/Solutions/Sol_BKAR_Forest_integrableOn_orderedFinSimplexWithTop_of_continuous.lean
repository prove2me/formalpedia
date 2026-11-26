-- Prove2me | solution 1 for BKAR.Forest.integrableOn_orderedFinSimplexWithTop_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:13.713554+00:00
-- url     : https://prove2.me/submissions/018c026b-2d7f-42fa-bdf8-56a4efaef859

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_isCompact_orderedFinSimplexWithTop

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {top : ℝ} {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    (hG : Continuous G) :
    IntegrableOn G (orderedFinSimplexWithTop top n) :=
  hG.continuousOn.integrableOn_compact (isCompact_orderedFinSimplexWithTop top n)
end BKAR.Forest
