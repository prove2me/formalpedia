-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedSupplyPoint_sub_quantile_le_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:40:43.240806+00:00
-- url     : https://prove2.me/submissions/56d328ce-3650-4941-a7d3-c1c9f99189b4

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyIndex_leaf_of_ne_zero
import Theorems.Thm_FD1D_SupplyConfiguration_quantile_mem_selectedCell

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hu0 : u ≠ 0) :
    |C.selectedSupplyPoint q fallback u - q.quantile u| ≤
      dyadicCellWidth L := by
  have hlabel :=
    C.selectedSupplyIndex_leaf_of_ne_zero q hq hsupport fallback hu hu0
  have hpoint := C.location_mem_cell (C.selectedSupplyIndex q fallback u)
  change C.selectedSupplyPoint q fallback u ∈
    dyadicCell (C.leaf (C.selectedSupplyIndex q fallback u)) at hpoint
  rw [hlabel] at hpoint
  have hquant := quantile_mem_selectedCell q hq hu
  rw [dyadicCell] at hpoint hquant
  rw [abs_le]
  constructor <;> linarith [hpoint.1, hpoint.2, hquant.1, hquant.2]
end FD1D.SupplyConfiguration
