-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i2_spatial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:35.595217+00:00
-- url     : https://prove2.me/submissions/e0697a84-7c13-4aaa-a813-cafa7387c593

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case10_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case1a_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case1b_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case2_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case3a_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case3b_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case3c_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case3d_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case4_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case5_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6a_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6aa_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6aaa_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6b_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6bb_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6bbb_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6c_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6cc_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case6ccc_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case7_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case8a_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case8b_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case8c_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case8d_regionTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i2_case9_regionTerm


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (ν : Fin 25)
    (hq : q * t ^ 2 = 1) (hd : d ≠ 0) (h : GeometricRange t d U V T) :
    HasSum (fun p : I2SpatialRow ν => i2SpatialTerm q t d U V T ν p.val)
      (i2RegionTerm ν t d (T * U) (T * V)) := by
  fin_cases ν
  · exact hasSum_i2_case1a_regionTerm q t d U V T hq hd h.t2 h.p
  · exact hasSum_i2_case1b_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case2_regionTerm q t d U V T hq hd h.t2 h.p h.g
  · exact hasSum_i2_case3a_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3b_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3c_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case3d_regionTerm q t d U V T hq hd h.t2 h.p h.e
  · exact hasSum_i2_case4_regionTerm q t d U V T hq hd h.t2 h.p h.e h.f
  · exact hasSum_i2_case5_regionTerm q t d U V T hq hd h.t2 h.p h.f h.g
  · exact hasSum_i2_case6a_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6aa_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6aaa_regionTerm q t d U V T hq hd h.t2 h.g
  · exact hasSum_i2_case6b_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6bb_regionTerm q t d U V T hq hd h.t2
  · exact hasSum_i2_case6bbb_regionTerm q t d U V T hq hd h.t2 h.g
  · exact hasSum_i2_case6c_regionTerm q t d U V T hq hd h.t2 h.n
  · exact hasSum_i2_case6cc_regionTerm q t d U V T hq hd h.t2 h.n
  · exact hasSum_i2_case6ccc_regionTerm q t d U V T hq hd h.t2 h.n h.g
  · exact hasSum_i2_case7_regionTerm q t d U V T hq hd h.t2 h.n h.g
  · exact hasSum_i2_case8a_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8b_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8c_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case8d_regionTerm q t d U V T hq hd h.t2 h.n h.e
  · exact hasSum_i2_case9_regionTerm q t d U V T hq hd h.t2 h.n h.e h.f
  · exact hasSum_i2_case10_regionTerm q t d U V T hq hd h.t2 h.n h.f h.g
end FourierJacobi.Analysis
