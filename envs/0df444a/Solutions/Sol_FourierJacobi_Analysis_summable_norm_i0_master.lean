-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i0_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:36.212677+00:00
-- url     : https://prove2.me/submissions/1579c8ce-63eb-47b1-9f3a-38f05332fa67

import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I0Master
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_full
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 0 p‖) := by
  apply latticeDepthEquiv.summable_iff.mp
  have hs := summable_norm_i0_full t d U V T h.t2 h.p h.n h.e h.f h.g
  have hd : Summable (fun c : ℕ => ‖if c = 0 then (1 : ℂ) else 0‖) := by
    simpa only [apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (α := ℝ) (β := ℕ) 0 1).summable
  convert hs.mul_norm hd using 1
  funext p
  simp only [masterTerm_zero, latticeDepthEquiv, Equiv.coe_fn_mk]
  split_ifs with hp <;> simp [hp]
end FourierJacobi.Analysis
