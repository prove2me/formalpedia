-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_master_sum_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:34.112142+00:00
-- url     : https://prove2.me/submissions/4f6d5851-a39c-4ec2-8583-598ad6422947

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_norm_le_undamped
import Theorems.Thm_FourierJacobi_Analysis_tendsto_masterTerm

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V : ℂ) (r : ℤ)
    (hs : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V 1 r p‖)) :
    Tendsto (fun T : ℝ => ∑' p : LatticeIndex, masterTerm q t d U V (T : ℂ) r p)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (∑' p : LatticeIndex, masterTerm q t d U V 1 r p)) := by
  apply tendsto_tsum_of_dominated_convergence hs (tendsto_masterTerm q t d U V r)
  filter_upwards [self_mem_nhdsWithin] with T hT
  intro p
  exact masterTerm_norm_le_undamped q t d U V r p hT.1.le hT.2.le
end FourierJacobi.Analysis
