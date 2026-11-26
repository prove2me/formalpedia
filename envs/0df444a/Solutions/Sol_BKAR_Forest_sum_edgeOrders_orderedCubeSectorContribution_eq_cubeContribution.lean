-- Prove2me | solution 1 for BKAR.Forest.sum_edgeOrders_orderedCubeSectorContribution_eq_cubeContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:32.861266+00:00
-- url     : https://prove2.me/submissions/646937ce-1e93-4a84-abbb-aab3ad2039cc

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Theorems.Thm_BKAR_Forest_cubeContribution_eq_sum_orderedCubeSectorContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    Finset.sum F.edgeOrders
      (fun order => F.orderedCubeSectorContribution order ρ) =
      F.cubeContribution ρ :=
  (F.cubeContribution_eq_sum_orderedCubeSectorContribution ρ hρ).symm
end BKAR.Forest
