-- Prove2me | solution 1 for FourierJacobi.Analysis.i1_master_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:00.225063+00:00
-- url     : https://prove2.me/submissions/d227c835-7d96-460d-8c7c-73c10609a4b2

import Definitions.Def_FourierJacobi_Analysis_I1Partition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i1_master
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1_master_of_geometricRange
import Theorems.Thm_FourierJacobi_Analysis_geometricRange_of_bounds


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t T : ℝ) (d U V : ℂ)
    (hqt : q*t^2=1) (ht0 : 0<t) (ht1 : t<1) (hT0 : 0≤T) (hT1 : T≤1)
    (hdlo : t≤‖d‖) (hdhi : ‖d‖≤1) (hstrict : T*t<‖d‖)
    (hU : ‖U‖=1) (hV : ‖V‖=1) :
    Summable (fun p : LatticeIndex => ‖masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1 p‖) ∧
    HasSum (masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1)
      (∑ i : Fin 15, regionTerms (t:ℂ) d ((T:ℂ)*U) ((T:ℂ)*V) ⟨10+i.val, by omega⟩) := by
  have h := geometricRange_of_bounds ht0 ht1 hT0 hT1 hdlo hdhi hstrict hU hV
  have he : (q:ℂ)*(t:ℂ)^2=1 := by exact_mod_cast hqt
  have ht : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le ht0 hdlo)
  exact ⟨summable_norm_i1_master q t d U V T ht he h,
    hasSum_i1_master_of_geometricRange q t d U V T hd he h⟩
end FourierJacobi.Analysis
