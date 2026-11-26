-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i2_spatial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:36:58.409226+00:00
-- url     : https://prove2.me/submissions/868f65a3-f8e1-499f-bf5f-fb8373a8f6e6

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case10
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case1a
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case1b
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case2
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case3a
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case3b
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case3c
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case3d
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case4
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case5
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6a
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6aa
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6aaa
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6b
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6bb
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6bbb
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6c
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6cc
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case6ccc
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case7
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case8a
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case8b
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case8c
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case8d
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_case9


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
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2SpatialTerm q t d U V T ν p.val‖) := by
  fin_cases ν
  · exact summable_norm_i2_case1a q t d U V T h.t2 h.p
  · exact summable_norm_i2_case1b q t d U V T h.t2
  · exact summable_norm_i2_case2 q t d U V T h.t2 h.p h.g
  · exact summable_norm_i2_case3a q t d U V T h.t2 h.p h.e
  · exact summable_norm_i2_case3b q t d U V T h.p h.e
  · exact summable_norm_i2_case3c q t d U V T h.p h.e
  · exact summable_norm_i2_case3d q t d U V T h.p h.e
  · exact summable_norm_i2_case4 q t d U V T h.p h.e h.f
  · exact summable_norm_i2_case5 q t d U V T h.p h.f h.g
  · exact summable_norm_i2_case6a q t d U V T h.t2
  · exact summable_norm_i2_case6aa q t d U V T h.t2
  · exact summable_norm_i2_case6aaa q t d U V T h.t2 h.g
  · exact summable_norm_i2_case6b q t d U V T h.t2
  · exact summable_norm_i2_case6bb q t d U V T h.t2
  · exact summable_norm_i2_case6bbb q t d U V T h.g
  · exact summable_norm_i2_case6c q t d U V T h.t2 h.n
  · exact summable_norm_i2_case6cc q t d U V T h.t2 h.n
  · exact summable_norm_i2_case6ccc q t d U V T h.n h.g
  · exact summable_norm_i2_case7 q t d U V T h.t2 h.n h.g
  · exact summable_norm_i2_case8a q t d U V T h.t2 h.n h.e
  · exact summable_norm_i2_case8b q t d U V T h.n h.e
  · exact summable_norm_i2_case8c q t d U V T h.n h.e
  · exact summable_norm_i2_case8d q t d U V T h.n h.e
  · exact summable_norm_i2_case9 q t d U V T h.n h.e h.f
  · exact summable_norm_i2_case10 q t d U V T h.n h.f h.g
end FourierJacobi.Analysis
