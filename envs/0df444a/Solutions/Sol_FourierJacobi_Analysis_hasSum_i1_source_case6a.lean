-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_i1_source_case6a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:42.603912+00:00
-- url     : https://prove2.me/submissions/15ce0ce9-7001-48c4-90ab-c694fc703665

import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I1SourceRows
import Theorems.Thm_FourierJacobi_Analysis_hasSum_i1r6a_master
import Theorems.Thm_FourierJacobi_Analysis_i1r6a_value_eq


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 8 => masterTerm q t d U V T 1 p.val)
      (regionTerms t d (T*U) (T*V) 17) := by
  have hs := hasSum_i1r6a_master q t d U V T ht hq0 hq1 hqt h
  rw [i1r6a_value_eq q t d U V T ht hd hqt h] at hs
  exact hs
end FourierJacobi.Analysis
