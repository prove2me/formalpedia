-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_central_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:15:36.207465+00:00
-- url     : https://prove2.me/submissions/d9f4b327-a61b-4e2e-b98d-6151362de167

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_master
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1_master
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_master


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q - 1 ≠ 0)
    (hq2 : q - 2 ≠ 0) (hqt : q * t ^ 2 = 1) (h : GeometricRange t d U V T)
    (r : Fin 3) : Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T (r.val : ℤ) p‖) := by
  fin_cases r
  · exact summable_norm_i0_master q t d U V T h
  · exact summable_norm_i1_master q t d U V T ht hqt h
  · exact summable_norm_i2_master q t d U V T ht hd hq0 hq1 hq2 hqt h
end FourierJacobi.Analysis
